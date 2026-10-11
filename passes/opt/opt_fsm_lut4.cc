#include "kernel/yosys.h"
#include "kernel/register.h"
#include "kernel/consteval.h"
#include "kernel/ff.h"
#include "kernel/mem.h"
#include "kernel/satgen.h"
#include "libs/ezsat/ezminisat.h"
#include "passes/fsm/fsmdata.h"
#include "opt_lut4_mapping.h"
#include "opt_lut4_feedback.h"
#include "muxledger.h"

#include <algorithm>
#include <array>
#include <charconv>
#include <memory>
#include <numeric>
#include <optional>
#if defined(__linux__) || defined(__FreeBSD__) || defined(__APPLE__)
#include <sys/resource.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using Lut4Mapping::capacity_add;
using Lut4Mapping::capacity_mul;

// 限额类别随原因一并显式传递，跳过计数不再从原因字符串反推。
enum class FsmLimitKind { Work, Memory, Deadline };

struct FsmLimits : Lut4Mapping::MappingBudget {
	int states = 64, initials = 256, transitions = 4096, nodes = 8192;
	int64_t sat = 2000000;
	int64_t analysis_work = 8000000, analysis_actual = 0;
	const char *limit_reason = "";
	FsmLimitKind limit_kind = FsmLimitKind::Work;
	void set_limit(FsmLimitKind kind, const char *reason) { limit_kind = kind; limit_reason = reason; }
	using Clock = std::chrono::steady_clock;
	Clock::time_point started = Clock::now(), deadline = Clock::time_point::max();
	std::function<void()> reclaim_memory;
	bool reserve(int64_t amount) {
		if (amount > memory - bytes && reclaim_memory) reclaim_memory();
		return Lut4Mapping::MappingBudget::reserve(amount);
	}
	bool time_available(double seconds = 0) const {
		log_assert(seconds >= 0);
		auto now = Clock::now();
		return now < deadline && std::chrono::duration<double>(deadline - now).count() >= seconds;
	}
	bool spend(int64_t amount) {
		log_assert(amount >= 0);
		if (!time_available()) { set_limit(FsmLimitKind::Deadline, "coordinator deadline"); return false; }
		if (amount > analysis_work) { set_limit(FsmLimitKind::Work, "analysis work allowance"); return false; }
		analysis_work -= amount; analysis_actual += amount; return true;
	}
	bool spend_mapping(int64_t amount) { return Lut4Mapping::MappingBudget::spend(amount); }
};

struct FsmStorage {
	FsmLimits &budget; int64_t bytes = 0;
	FsmStorage(FsmLimits &budget) : budget(budget) {}
	bool reserve(int64_t amount) { if (!budget.reserve(amount)) { budget.set_limit(FsmLimitKind::Memory, "workspace memory allowance"); return false; } bytes = capacity_add(bytes, amount); return true; }
	void reserve_required(int64_t amount) {
		if (amount > budget.memory - budget.bytes && budget.reclaim_memory) budget.reclaim_memory();
		budget.reserve_required(amount); bytes = capacity_add(bytes, amount);
	}
	void resize_required(int64_t amount) {
		log_assert(amount >= 0);
		if (amount > bytes) reserve_required(amount - bytes);
		else { budget.bytes -= bytes - amount; bytes = amount; }
	}
	bool resize(int64_t amount) {
		log_assert(amount >= 0);
		if (amount > bytes) return reserve(amount - bytes);
		budget.bytes -= bytes - amount; bytes = amount; return true;
	}
	~FsmStorage() { budget.bytes -= bytes; log_assert(budget.bytes >= 0); }
};

enum class FsmProofStatus { Proved, Disproved, LimitReached, Unsupported };

struct FsmProofResult {
	FsmProofStatus status;
	const char *reason;
	bool proved() const { return status == FsmProofStatus::Proved; }
	const char *name() const {
		switch (status) {
		case FsmProofStatus::Proved: return "Proved";
		case FsmProofStatus::Disproved: return "Disproved";
		case FsmProofStatus::LimitReached: return "LimitReached";
		case FsmProofStatus::Unsupported: return "Unsupported";
		}
		log_abort();
	}
};

using FsmSignal = std::vector<std::pair<IdString, int>>;
static FsmSignal save_signal(const SigSpec &sig) {
	FsmSignal result;
	for (auto bit : sig) result.emplace_back(bit.wire ? bit.wire->name : IdString(), bit.wire ? bit.offset : int(bit.data));
	return result;
}
static SigSpec load_signal(Module *module, const FsmSignal &sig) {
	SigSpec result;
	for (auto bit : sig) {
		if (bit.first.empty()) result.append(State(bit.second));
		else { auto wire = module->wire(bit.first); log_assert(wire); result.append(SigBit(wire, bit.second)); }
	}
	return result;
}

struct FsmModel {
	IdString module, cell;
	FsmData data;
	SigSpec inputs, outputs, q, d;
	std::vector<IdString> removed;
	std::vector<int> initial;
	FsmSignal saved_inputs, saved_outputs;
	std::string fsm_name;
	int width_limit = 0;
	bool extracted = false;
};

static int64_t ast_capacity(const AST::AstNode *node)
{
	if (!node) return 0;
	int64_t bytes = capacity_add(sizeof(*node), node->str.capacity());
	bytes = capacity_add(bytes, capacity_mul(node->bits.capacity(), sizeof(State)));
	bytes = capacity_add(bytes, capacity_mul(node->children.capacity(), sizeof(std::unique_ptr<AST::AstNode>)));
	bytes = capacity_add(bytes, capacity_mul(node->dimensions.capacity(), sizeof(AST::AstNode::dimension_t)));
	for (auto &child : node->children) bytes = capacity_add(bytes, ast_capacity(child.get()));
	for (auto &attribute : node->attributes) bytes = capacity_add(bytes, capacity_add(128, ast_capacity(attribute.second.get())));
	return bytes;
}

static int64_t module_capacity(Module *module)
{
	int64_t bytes = sizeof(Module) + 256;
	auto attributes = [&](const dict<IdString, Const> &values) {
		for (auto &item : values) bytes = capacity_add(bytes, capacity_add(128, capacity_mul(GetSize(item.second), sizeof(State))));
	};
	attributes(module->attributes); attributes(module->parameter_default_values);
	if (auto ast = dynamic_cast<AST::AstModule *>(module)) bytes = capacity_add(bytes, ast_capacity(ast->ast.get()));
	for (auto wire : module->wires()) { bytes = capacity_add(bytes, sizeof(Wire) + 128); attributes(wire->attributes); }
	for (auto cell : module->cells()) {
		bytes = capacity_add(bytes, sizeof(Cell) + 256); attributes(cell->attributes); attributes(cell->parameters);
		for (auto &port : cell->connections()) bytes = capacity_add(bytes, capacity_add(128, capacity_mul(GetSize(port.second), sizeof(SigBit))));
	}
	for (auto &connection : module->connections()) bytes = capacity_add(bytes, capacity_add(128, capacity_mul(capacity_add(GetSize(connection.first), GetSize(connection.second)), sizeof(SigBit))));
	bytes = capacity_add(bytes, capacity_mul(module->memories.size(), sizeof(RTLIL::Memory) + 128));
	return bytes;
}
static int64_t modules_capacity(Design *design) {
	int64_t result = 0;
	for (auto module : design->modules()) result = capacity_add(result, module_capacity(module));
	return result;
}
static int64_t design_capacity(Design *design, int64_t *modules = nullptr)
{
	int64_t modules_bytes = modules_capacity(design);
	if (modules != nullptr) *modules = modules_bytes;
	int64_t bytes = capacity_add(sizeof(Design), modules_bytes);
	for (auto &node : design->verilog_packages) bytes = capacity_add(bytes, ast_capacity(node.get()));
	for (auto &node : design->verilog_globals) bytes = capacity_add(bytes, ast_capacity(node.get()));
	for (auto &item : design->scratchpad) bytes = capacity_add(bytes, capacity_add(128, capacity_add(item.first.capacity(), item.second.capacity())));
	bytes = capacity_add(bytes, capacity_add(capacity_mul(design->selection_stack.capacity(), sizeof(RTLIL::Selection)), design->selected_active_module.capacity()));
	auto selection = [&](const RTLIL::Selection &value) {
		bytes = capacity_add(bytes, capacity_mul(value.selected_modules.size(), 128));
		for (auto &item : value.selected_members) bytes = capacity_add(bytes, capacity_add(128, capacity_mul(item.second.size(), 128)));
	};
	for (auto &value : design->selection_stack) selection(value);
	for (auto &item : design->selection_vars) { bytes = capacity_add(bytes, 128); selection(item.second); }
	return bytes;
}

// design -stash 保存 modules 与 Selection，独立全局 AST 保持当前对象的计价。
static int64_t abc_clone_capacity(Design *design) {
	int64_t bytes = capacity_add(sizeof(Design), modules_capacity(design));
	bytes = capacity_add(bytes, capacity_mul(design->selection_stack.capacity(), sizeof(RTLIL::Selection)));
	bytes = capacity_add(bytes, design->selected_active_module.capacity());
	auto selection = [&](const RTLIL::Selection &value) {
		bytes = capacity_add(bytes, capacity_mul(value.selected_modules.size(), 128));
		for (auto &item : value.selected_members) bytes = capacity_add(bytes, capacity_add(128, capacity_mul(item.second.size(), 128)));
	};
	for (auto &value : design->selection_stack) selection(value);
	for (auto &item : design->selection_vars) { bytes = capacity_add(bytes, 128); selection(item.second); }
	return bytes;
}

// 三份 helper 分别计价；接口、白盒内容和每个实例的输出连接均保留。
static std::array<int64_t, 3> abc_helper_capacity(Design *design, bool sequential) {
	std::array<int64_t, 3> result {{sizeof(Design) + 1024, sizeof(Design) + 1024, sizeof(Design) + 1024}};
	for (auto module : design->selected_modules()) {
		std::set<IdString> bodies;
		int64_t holes = sizeof(Module) + 256;
		for (auto cell : module->cells()) {
			auto definition = design->module(cell->type);
			if (!definition) continue;
			bool flop = sequential && definition->get_bool_attribute(ID::abc9_flop);
			bool box = definition->get_bool_attribute(ID::abc9_box);
			bool bypass = definition->get_bool_attribute(ID::abc9_bypass);
			bool timing = false;
			for (auto item : definition->cells()) if (item->type.in(ID($specify2), ID($specify3), ID($specrule))) { timing = true; break; }
			if (!flop && !box && !bypass && !timing) continue;
			int64_t interface = sizeof(Module) + 256 + 2 * (sizeof(Cell) + 256);
			for (auto &port : cell->connections()) {
				int64_t width = GetSize(port.second);
				interface = capacity_add(interface, capacity_add(3 * (sizeof(Wire) + 128), capacity_mul(width, 3 * (128 + sizeof(SigBit)))));
				holes = capacity_add(holes, capacity_add(sizeof(Wire) + 256, capacity_mul(width, 2 * sizeof(SigBit))));
			}
			for (auto &parameter : cell->parameters) interface = capacity_add(interface, capacity_add(128, capacity_mul(GetSize(parameter.second), sizeof(State))));
			result[1] = capacity_add(result[1], interface);
			if (bypass || flop) result[0] = capacity_add(result[0], capacity_add(interface, module_capacity(definition)));
			if (bodies.insert(cell->type).second) holes = capacity_add(holes, module_capacity(definition));
		}
		result[2] = capacity_add(result[2], holes);
	}
	return result;
}

static int64_t design_ast_capacity(Design *design) {
	int64_t result = 0;
	for (auto module : design->modules()) if (auto ast = dynamic_cast<AST::AstModule *>(module)) result = capacity_add(result, ast_capacity(ast->ast.get()));
	for (auto &node : design->verilog_packages) result = capacity_add(result, ast_capacity(node.get()));
	for (auto &node : design->verilog_globals) result = capacity_add(result, ast_capacity(node.get()));
	return result;
}

static int64_t mux_index_capacity(Design *design) {
	int64_t result = 0;
	for (auto module : design->selected_unboxed_modules()) {
		int64_t bits = 0, occurrences = 0, metadata = 0;
		for (auto wire : module->wires()) bits = capacity_add(bits, wire->width);
		for (auto cell : module->cells()) {
			for (auto &port : cell->connections()) occurrences = capacity_add(occurrences, GetSize(port.second));
			metadata = capacity_add(metadata, capacity_add(cell->connections().size(), capacity_add(cell->parameters.size(), cell->attributes.size())));
		}
		result = std::max(result, capacity_add(capacity_mul(bits, 128), capacity_add(capacity_mul(occurrences, 256), capacity_add(capacity_mul(metadata, 256), capacity_mul(module->cells_size(), 1024)))));
	}
	return result;
}
static int64_t post_capacity(Design *design, bool cell_indexes) {
	int64_t result = 0;
	for (auto module : design->selected_unboxed_modules()) {
		int64_t index = Lut4Mapping::post_index_bytes(module, cell_indexes);
		// resyn 的函数索引行容器和排序队列与 Pass 构造前的预付保持一致。
		if (cell_indexes) index = capacity_add(index, capacity_mul(1024, module->cells_size()));
		result = std::max(result, index);
	}
	return result;
}
static int64_t post_phase_capacity(int64_t index, int64_t workspace_limit, int64_t available, bool required = false) {
	log_assert(index >= 0 && workspace_limit >= 0 && available >= 0);
	int64_t workspace = required ? workspace_limit : std::min(workspace_limit, std::max<int64_t>(0, available - index));
	return capacity_add(index, workspace);
}
static int64_t carry_capacity(Design *design) {
	int64_t result = 0;
	for (auto module : design->selected_unboxed_modules()) result = std::max(result, Lut4Mapping::carry_index_bytes(module));
	return result;
}
static int64_t carry_workspace_limit(Design *design, int64_t index) {
	int64_t total = std::min(Lut4Mapping::post_carry_workspace,
		capacity_add(8 * 1048576, capacity_mul(8192, Lut4Mapping::carry_scale(design))));
	return std::max<int64_t>(0, total - index);
}
static int64_t process_peak_bytes() {
#if defined(__linux__) || defined(__FreeBSD__) || defined(__APPLE__)
	struct rusage usage;
	if (getrusage(RUSAGE_SELF, &usage) != 0) log_error("opt_fsm_lut4: getrusage(RUSAGE_SELF) failed.\n");
#if defined(__APPLE__)
	return capacity_mul(usage.ru_maxrss, 1);
#else
	return capacity_mul(usage.ru_maxrss, 1024);
#endif
#else
	log_error("opt_fsm_lut4: process peak measurement requires a supported getrusage platform.\n");
#endif
}

using Lut4Mapping::clone_design;

struct FsmIndex {
	Module *module;
	SigMap sigmap;
	CellTypes types;
	dict<SigBit, pool<Cell *>> drivers, users;
	pool<SigBit> protected_bits;
	FsmIndex(Module *module) : module(module), sigmap(module) {
		types.setup_internals();
		types.setup_internals_mem();
		types.setup_internals_anyinit();
		types.setup_stdcells();
		for (auto wire : module->wires())
			if (wire->port_id || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire)) protected_bits.insert(bit);
		for (auto cell : module->cells()) {
			for (auto &port : cell->connections()) {
				bool out = types.cell_known(cell->type) && types.cell_output(cell->type, port.first);
				for (auto bit : sigmap(port.second)) if (bit.wire) {
					if (out) drivers[bit].insert(cell); else users[bit].insert(cell);
					if (cell->get_bool_attribute(ID::keep)) protected_bits.insert(bit);
				}
			}
		}
		for (auto wire : module->wires()) if (wire->attributes.count(ID::init))
			for (auto bit : sigmap(wire)) protected_bits.insert(bit);
	}
	Cell *driver(const SigSpec &sig) {
		Cell *result = nullptr;
		for (auto bit : sigmap(sig)) if (bit.wire) {
			if (!drivers.count(bit) || GetSize(drivers.at(bit)) != 1) return nullptr;
			auto cell = *drivers.at(bit).begin();
			if (result && result != cell) return nullptr;
			result = cell;
		}
		return result;
	}
};

static bool expand_state_roms(Design *design, FsmLimits &budget)
{
	RTLIL::Selection selection(false);
	for (auto module : design->selected_modules()) {
		FsmIndex index(module);
		for (auto &mem : Mem::get_all_memories(module)) {
			if (!mem.wr_ports.empty() || GetSize(mem.rd_ports) != 1 || mem.width < 2 || mem.width > 16 || mem.size > budget.initials || mem.get_bool_attribute(ID::keep)) continue;
			auto &read = mem.rd_ports.front();
			if (read.clk_enable || !read.en.is_fully_ones() || read.get_bool_attribute(ID::keep)) continue;
			auto address = index.sigmap(read.addr);
			auto driver = index.driver(address);
			if (!driver || !StaticCellTypes::categories.is_ff(driver->type) || index.sigmap(driver->getPort(ID::Q)) != address) continue;
			if (!mem.get_init_data().is_fully_def()) continue;
			if (!budget.spend(int64_t(mem.size) * mem.width * 32)) return false;
			selection.selected_members[module->name].insert(mem.memid);
			log("opt_fsm_lut4: expanding constant state ROM %s.%s (%d words).\n", log_id(module), log_id(mem.memid), mem.size);
		}
	}
	if (!selection.empty()) Pass::call_on_selection(design, selection, "memory_map -rom-only");
	return true;
}

struct FsmExtractor {
	FsmIndex &index;
	FsmLimits &budget;
	FsmModel model;
	pool<Cell *> tree, comparisons, visiting;
	std::map<Const, int> states;
	FsmExtractor(FsmIndex &index, FsmLimits &budget) : index(index), budget(budget) {}
	bool add_state(Const state) {
		if (!state.is_fully_def()) return false;
		if (!states.count(state)) {
			if (GetSize(states) >= budget.states) return false;
			states[state] = GetSize(model.data.state_table);
			model.data.state_table.push_back(state);
		}
		return true;
	}
	bool find_tree(SigSpec sig, int depth = 0) {
		if (!budget.spend(GetSize(sig) + 1) || depth > 128) return false;
		sig = index.sigmap(sig);
		if (sig == model.q) return true;
		if (sig.is_fully_const()) return add_state(sig.as_const());
		auto cell = index.driver(sig);
		if (!cell || cell->get_bool_attribute(ID::keep) || !cell->type.in(ID($mux), ID($pmux))) return false;
		if (index.sigmap(cell->getPort(ID::Y)) != sig || visiting.count(cell)) return false;
		if (tree.count(cell)) return true;
		visiting.insert(cell);
		auto a = index.sigmap(cell->getPort(ID::A));
		auto b = index.sigmap(cell->getPort(ID::B));
		if (GetSize(a) != GetSize(model.q) || GetSize(b) % GetSize(a)) return false;
		if (!find_tree(a, depth + 1)) return false;
		for (int i = 0; i < GetSize(b); i += GetSize(a)) if (!find_tree(b.extract(i, GetSize(a)), depth + 1)) return false;
		model.inputs.append(index.sigmap(cell->getPort(ID::S)));
		visiting.erase(cell); tree.insert(cell);
		return true;
	}
	bool transitions(ConstEval &ce, int state, Const cube, int depth = 0) {
		if (!budget.spend(1 + index.module->cells_size()) || depth > 128 || GetSize(model.data.transition_table) >= budget.transitions) return false;
		auto d = model.d, outputs = model.outputs;
		SigSpec undef;
		bool done = ce.eval(d, undef);
		if (done) done = ce.eval(outputs, undef);
		if (done) {
			if (!d.is_fully_def() || !outputs.is_fully_const() || !add_state(d.as_const())) return false;
			model.data.transition_table.push_back({state, states.at(d.as_const()), cube, outputs.as_const()});
			return true;
		}
		int chosen = -1;
		for (auto bit : undef) {
			for (int i = 0; i < GetSize(model.inputs); i++)
				if (bit == model.inputs[i] && cube[i] == State::Sa) { chosen = i; break; }
			if (chosen >= 0) break;
		}
		if (chosen < 0) return false;
		for (auto value : {State::S0, State::S1}) {
			auto begin = model.data.transition_table.size();
			ce.push(); ce.set(model.inputs[chosen], Const(value)); cube.set(chosen, value);
			bool success = transitions(ce, state, cube, depth + 1); ce.pop();
			if (!success) return false;
			if (value == State::S1 && begin > 0 && model.data.transition_table.size() == begin + 1) {
				auto &left = model.data.transition_table[begin - 1], &right = model.data.transition_table.back();
				if (!budget.spend(GetSize(cube) + model.data.num_outputs + 1)) return false;
				Const merged = left.ctrl_in; merged.set(chosen, State::S1);
				if (left.state_in == right.state_in && left.state_out == right.state_out && left.ctrl_out == right.ctrl_out && merged == right.ctrl_in) {
					left.ctrl_in.set(chosen, State::Sa); model.data.transition_table.pop_back();
				}
			}
		}
		return true;
	}
	bool run(Cell *cell) {
		if (cell->get_bool_attribute(ID::keep)) return false;
		FfInitVals initvals(&index.sigmap, index.module);
		FfData ff(&initvals, cell);
		if (!ff.has_clk || ff.has_gclk || ff.has_aload || ff.has_sr || ff.is_fine || ff.width < 2 || ff.width > 16) return false;
		model.module = index.module->name; model.cell = cell->name; model.extracted = true;
		model.q = index.sigmap(ff.sig_q); model.d = index.sigmap(ff.sig_d);
		SigSpec controls = ff.sig_clk;
		if (ff.has_ce) controls.append(ff.sig_ce);
		if (ff.has_arst) controls.append(ff.sig_arst);
		if (ff.has_srst) controls.append(ff.sig_srst);
		if (index.sigmap(controls).extract(model.q).size()) return false;
		for (auto bit : model.q)
			if (!bit.wire || !index.drivers.count(bit) || GetSize(index.drivers.at(bit)) != 1) return false;
		for (auto wire : index.module->wires()) if (index.sigmap(wire).extract(model.q).size()) {
			if (wire->port_id || wire->get_bool_attribute(ID::keep)) return false;
			auto it = wire->attributes.find(ID::fsm_encoding);
			if (it != wire->attributes.end() && (it->second.decode_string() == "none" || it->second.decode_string() == "user")) return false;
		}
		if (!find_tree(model.d)) return false;
		for (auto item : tree) for (auto bit : index.sigmap(item->getPort(ID::Y))) {
			if (index.protected_bits.count(bit)) return false;
			if (index.users.count(bit)) for (auto user : index.users.at(bit)) if (user != cell && !tree.count(user)) return false;
		}
		if (ff.has_arst && !add_state(ff.val_arst)) return false;
		if (ff.has_srst && !add_state(ff.val_srst)) return false;
		// 所有原允许初始代码都进入闭包，包括没有 init 的完整代码空间。
		int unknown = 0;
		for (auto bit : ff.val_init) if (bit == State::Sx) unknown++; else if (bit != State::S0 && bit != State::S1) return false;
		if ((1 << unknown) > budget.initials) return false;
		for (int value = 0; value < (1 << unknown); value++) {
			Const state = ff.val_init; int pos = 0;
			for (int bit = 0; bit < ff.width; bit++) if (state[bit] == State::Sx) state.set(bit, ((value >> pos++) & 1) ? State::S1 : State::S0);
			if (!add_state(state)) return false;
			model.initial.push_back(states.at(state));
		}
		pool<Cell *> q_users;
		for (auto bit : model.q) if (index.users.count(bit)) for (auto user : index.users.at(bit)) q_users.insert(user);
		for (auto user : q_users) {
			if (user == cell || tree.count(user)) continue;
			if (user->get_bool_attribute(ID::keep) || !user->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool))) return false;
			auto a = index.sigmap(user->getPort(ID::A));
			if (user->hasPort(ID::B)) {
				auto b = index.sigmap(user->getPort(ID::B));
				if (a != model.q && b != model.q) return false;
				if (a == model.q ? !b.is_fully_def() : !a.is_fully_def()) return false;
			} else if (a != model.q) return false;
			auto y = index.sigmap(user->getPort(ID::Y));
			for (auto wire : index.module->wires()) if ((wire->get_bool_attribute(ID::keep) || wire->attributes.count(ID::init)) && index.sigmap(wire).extract(y).size()) return false;
			for (auto bit : y) if (!index.drivers.count(bit) || GetSize(index.drivers.at(bit)) != 1) return false;
			comparisons.insert(user); model.outputs.append(y);
		}
		model.inputs.sort_and_unify(); model.outputs.sort_and_unify(); model.inputs.remove(model.outputs);
		model.inputs.remove(model.q);
		if (GetSize(model.inputs) > 128 || GetSize(model.outputs) > 256) return false;
		for (auto bit : model.inputs) if (!bit.wire) return false;
		model.data.state_bits = ff.width; model.data.num_inputs = GetSize(model.inputs); model.data.num_outputs = GetSize(model.outputs); model.data.reset_state = -1;
		ConstEval ce(index.module); ce.stop(model.inputs);
		for (int state = 0; state < GetSize(model.data.state_table); state++) {
			ce.push(); ce.set(model.q, model.data.state_table[state]);
			bool success = transitions(ce, state, Const(State::Sa, GetSize(model.inputs))); ce.pop();
			if (!success) return false;
		}
		for (auto item : comparisons) model.removed.push_back(item->name);
		return GetSize(states) > 1;
	}
};

struct FsmDag {
	struct Node { int var, lo, hi; };
	struct Cube { Const bits; State value; };
	std::vector<Node> nodes {{-1, 0, 0}, {-1, 1, 1}, {-1, 2, 2}};
	std::map<std::tuple<int, int, int>, int> unique;
	FsmLimits &budget;
	FsmStorage storage;
	bool complete = true;
	bool conflicting_cubes = false;
	const char *limit_reason = "";
	struct Lut { std::vector<int> leaves; Const table; };
	dict<int, Lut> luts;
	std::map<std::pair<std::vector<int>, Const>, int> lut_cache;
	FsmDag(FsmLimits &budget) : budget(budget), storage(budget) {}
	FsmProofResult failure() const {
		log_assert(!complete);
		if (conflicting_cubes) return {FsmProofStatus::Unsupported, "overlapping cubes require conflicting output values"};
		log_assert(limit_reason[0]);
		return {FsmProofStatus::LimitReached, limit_reason};
	}
	int node(int var, int lo, int hi) {
		if (lo == hi) return lo;
		auto key = std::make_tuple(var, lo, hi);
		auto found = unique.find(key); if (found != unique.end()) return found->second;
		if (GetSize(nodes) >= budget.nodes) { complete = false; limit_reason = "DAG node allowance"; return 2; }
		if (!budget.spend(1) || !storage.reserve(192)) { complete = false; limit_reason = budget.limit_reason; return 2; }
		int result = GetSize(nodes); nodes.push_back({var, lo, hi}); unique.emplace(key, result); return result;
	}
	int build(const std::vector<Cube> &cubes) {
		if (cubes.empty()) return 2;
		if (!budget.spend(GetSize(cubes) * (GetSize(cubes.front().bits) + 1))) { complete = false; limit_reason = budget.limit_reason; return 2; }
		FsmStorage temporary(budget);
		if (!temporary.reserve(int64_t(GetSize(cubes)) * (256 + 2 * GetSize(cubes.front().bits)))) { complete = false; limit_reason = budget.limit_reason; return 2; }
		State common = State::Sx; bool uniform = true;
		for (auto &cube : cubes) if (cube.value != State::Sx) {
			if (common != State::Sx && common != cube.value) uniform = false;
			common = cube.value;
		}
		if (uniform) return common == State::S0 ? 0 : common == State::S1 ? 1 : 2;
		int var = -1;
		for (auto &cube : cubes) for (int bit = 0; bit < GetSize(cube.bits); bit++)
			if (cube.bits[bit] == State::S0 || cube.bits[bit] == State::S1) { if (var < 0 || bit < var) var = bit; }
		if (var < 0) {
			complete = false;
			conflicting_cubes = true;
			return 2;
		}
		std::vector<Cube> low, high;
		for (auto cube : cubes) {
			auto value = cube.bits[var]; cube.bits.set(var, State::Sa);
			if (value != State::S1) low.push_back(cube);
			if (value != State::S0) high.push_back(cube);
		}
		int lo = build(low), hi = build(high);
		return node(var, lo, hi);
	}
	std::vector<int> functions(const FsmModel &model, const std::vector<Const> &codes) {
		std::vector<int> roots;
		for (int bit = 0; bit < GetSize(codes.front()) + model.data.num_outputs; bit++) {
			std::vector<Cube> cubes;
			for (auto &tr : model.data.transition_table) {
				if (tr.state_in < 0 || tr.state_out < 0 || tr.state_in >= GetSize(codes) || tr.state_out >= GetSize(codes))
					log_error("opt_fsm_lut4: invalid transition state index for %s.%s.\n", log_id(model.module), log_id(model.cell));
				Const pattern = codes.at(tr.state_in); pattern.append(tr.ctrl_in);
				State value = bit < GetSize(codes.front()) ? codes.at(tr.state_out)[bit] : tr.ctrl_out[bit - GetSize(codes.front())];
				if (value == State::Sa) value = State::Sx;
				if (value != State::S0 && value != State::S1 && value != State::Sx)
					log_error("opt_fsm_lut4: invalid transition output state for %s.%s.\n", log_id(model.module), log_id(model.cell));
				cubes.push_back({pattern, value});
			}
			roots.push_back(build(cubes));
			if (!complete) return {};
		}
		return roots;
	}
	// 一个 cut 同时覆盖译码与选择；所有输出共用节点及互补函数缓存。
	std::vector<int> cut(int root) const {
		std::vector<int> leaves;
		if (root < 3) return leaves;
		if (luts.count(root)) return luts.at(root).leaves;
		leaves = {nodes[root].var, -nodes[root].lo - 1, -nodes[root].hi - 1};
		auto normalize = [&]() {
			leaves.erase(std::remove_if(leaves.begin(), leaves.end(), [](int item) { return item < 0 && -item - 1 < 3; }), leaves.end());
			std::sort(leaves.begin(), leaves.end()); leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
		};
		normalize();
		bool changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i < GetSize(leaves); i++) if (leaves[i] < 0 && !luts.count(-leaves[i] - 1)) {
				auto saved = leaves; auto item = nodes[-leaves[i] - 1]; leaves.erase(leaves.begin() + i);
				leaves.insert(leaves.end(), {item.var, -item.lo - 1, -item.hi - 1}); normalize();
				if (GetSize(leaves) <= 4) { changed = true; break; }
				leaves = std::move(saved);
			}
		}
		return leaves;
	}
	State eval_cut(int root, const std::vector<int> &leaves, int row) const {
		if (root < 3) return root == 0 ? State::S0 : root == 1 ? State::S1 : State::Sx;
		for (int i = 0; i < GetSize(leaves); i++) if (leaves[i] == -root - 1) return (row >> i) & 1 ? State::S1 : State::S0;
		if (luts.count(root)) {
			int index = 0;
			for (int i = 0; i < GetSize(luts.at(root).leaves); i++) {
				auto found = std::find(leaves.begin(), leaves.end(), luts.at(root).leaves[i]); log_assert(found != leaves.end());
				index |= ((row >> (found - leaves.begin())) & 1) << i;
			}
			return luts.at(root).table[index];
		}
		auto item = nodes[root]; int pos = -1;
		for (int i = 0; i < GetSize(leaves); i++) if (leaves[i] == item.var) pos = i;
		log_assert(pos >= 0);
		return eval_cut((row >> pos) & 1 ? item.hi : item.lo, leaves, row);
	}
	void support(int root, pool<int> &result, pool<int> &seen) const {
		if (root < 3 || seen.count(root)) return;
		seen.insert(root);
		if (luts.count(root)) {
			for (int leaf : luts.at(root).leaves) if (leaf >= 0) result.insert(leaf); else support(-leaf - 1, result, seen);
		} else { result.insert(nodes[root].var); support(nodes[root].lo, result, seen); support(nodes[root].hi, result, seen); }
	}
	State eval_vars(int root, const std::vector<int> &variables, int row) const {
		if (root < 3) return root == 0 ? State::S0 : root == 1 ? State::S1 : State::Sx;
		if (luts.count(root)) {
			int index = 0;
			for (int i = 0; i < GetSize(luts.at(root).leaves); i++) {
				int leaf = luts.at(root).leaves[i];
				State value = leaf >= 0 ? (((row >> (std::find(variables.begin(), variables.end(), leaf) - variables.begin())) & 1) ? State::S1 : State::S0) : eval_vars(-leaf - 1, variables, row);
				if (value == State::Sx) return State::Sx;
				if (value == State::S1) index |= 1 << i;
			}
			return luts.at(root).table[index];
		}
		auto pos = std::find(variables.begin(), variables.end(), nodes[root].var); log_assert(pos != variables.end());
		return eval_vars((row >> (pos - variables.begin())) & 1 ? nodes[root].hi : nodes[root].lo, variables, row);
	}
	int add_lut(std::vector<int> leaves, Const table) {
		// 去除无关输入，使各输出分别使用所需的中间函数子集。
		for (int bit = GetSize(leaves) - 1; bit >= 0; bit--) {
			bool unused = true;
			for (int row = 0; row < GetSize(table); row++) if (!(row & (1 << bit)) && table[row] != table[row | (1 << bit)]) { unused = false; break; }
			if (!unused) continue;
			Const reduced;
			for (int row = 0; row < GetSize(table); row++) if (!(row & (1 << bit))) reduced.append(Const(table[row]));
			leaves.erase(leaves.begin() + bit); table = std::move(reduced);
		}
		if (leaves.empty()) return table[0] == State::S0 ? 0 : table[0] == State::S1 ? 1 : 2;
		if (GetSize(leaves) == 1 && table[0] == State::S0 && table[1] == State::S1)
			return leaves[0] >= 0 ? node(leaves[0], 0, 1) : -leaves[0] - 1;
		auto key = std::make_pair(leaves, table);
		auto cached = lut_cache.find(key); if (cached != lut_cache.end()) return cached->second;
		if (GetSize(nodes) >= budget.nodes) { complete = false; limit_reason = "DAG node allowance"; return 2; }
		if (!storage.reserve(256 + GetSize(table)) || !budget.spend(GetSize(table))) { complete = false; limit_reason = budget.limit_reason; return 2; }
		int result = GetSize(nodes); nodes.push_back({-2, 0, 0}); lut_cache.emplace(std::move(key), result); luts[result] = {std::move(leaves), std::move(table)}; return result;
	}
	// 对联合输出的余因子列搜索共享输入及一、两个中间编码函数。
	void decompose(std::vector<int> &roots) {
		if (!budget.spend(int64_t(GetSize(roots)) * (nodes.size() + GetSize(roots) * 192))) return;
		std::vector<pool<int>> supports(GetSize(roots));
		for (int i = 0; i < GetSize(roots); i++) { pool<int> seen; support(roots[i], supports[i], seen); }
		std::vector<int> order; pool<int> used;
		while (GetSize(order) < GetSize(roots)) {
			pool<int> combined;
			for (int member = 0; member < 8 && GetSize(order) < GetSize(roots); member++) {
				int selected = -1, score = -1;
				for (int i = 0; i < GetSize(roots); i++) if (!used.count(i)) {
					int overlap = 0; for (int bit : supports[i]) if (combined.count(bit)) overlap++;
					if (selected < 0 || overlap > score) { selected = i; score = overlap; }
				}
				used.insert(selected); order.push_back(selected);
				for (int bit : supports[selected]) combined.insert(bit);
			}
		}
		std::vector<int> grouped; for (int i : order) grouped.push_back(roots[i]);
		decompose_ordered(grouped);
		for (int i = 0; i < GetSize(order); i++) roots[order[i]] = grouped[i];
	}
	void decompose_ordered(std::vector<int> &roots) {
		for (int begin = 0; begin < GetSize(roots); begin += 8) {
			int end = std::min(begin + 8, GetSize(roots)); pool<int> support_bits, seen;
			for (int i = begin; i < end; i++) support(roots[i], support_bits, seen);
			std::vector<int> vars(support_bits.begin(), support_bits.end()); std::sort(vars.begin(), vars.end());
			int n = GetSize(vars); if (n <= 4 || n > 10) continue;
			FsmStorage temporary(budget); if (!temporary.reserve((end - begin) * (1 << n) * 8)) continue;
			std::vector<std::vector<State>> tables(end - begin, std::vector<State>(1 << n));
			if (!budget.spend((end - begin) * (1 << n) * n)) continue;
			for (int row = 0; row < (1 << n); row++) for (int i = begin; i < end; i++) {
				auto value = eval_vars(roots[i], vars, row); tables[i - begin][row] = value == State::S1 ? State::S1 : State::S0;
			}
			int original_cost = cost(roots); std::vector<int> best_roots = roots;
			int trials = 0;
			for (int free_mask = 0; free_mask < (1 << n) && trials < 32; free_mask++) {
				int free_size = __builtin_popcount(unsigned(free_mask)); if (free_size > 3 || free_size < std::max(0, n - 8)) continue;
				for (int shared = -1; shared < n && trials < 32; shared++) {
					if (shared >= 0 && !(free_mask & (1 << shared))) continue;
					trials++; std::vector<int> bound, free;
					for (int i = 0; i < n; i++) { if (!(free_mask & (1 << i)) || i == shared) bound.push_back(i); if (free_mask & (1 << i)) free.push_back(i); }
					if (GetSize(bound) > 8 || !budget.spend((1 << n) * (end - begin))) break;
					std::map<std::vector<State>, int> columns; std::vector<int> classes(1 << GetSize(bound));
					for (int b = 0; b < GetSize(classes); b++) {
						std::vector<State> column;
						for (int f = 0; f < (1 << GetSize(free)); f++) {
							int row = 0; for (int i = 0; i < GetSize(bound); i++) row |= ((b >> i) & 1) << bound[i];
							for (int i = 0; i < GetSize(free); i++) if (free[i] != shared) row |= ((f >> i) & 1) << free[i];
							for (auto &table : tables) column.push_back(table[row]);
						}
						auto found = columns.find(column);
						if (found == columns.end()) { int id = GetSize(columns); columns.emplace(std::move(column), id); classes[b] = id; }
						else classes[b] = found->second;
					}
					int bridge_count = GetSize(columns) <= 2 ? 1 : GetSize(columns) <= 4 ? 2 : 3;
					if (bridge_count + GetSize(free) > 4 || bridge_count > 2) continue;
					std::vector<int> numbering(1 << bridge_count); std::iota(numbering.begin(), numbering.end(), 0);
					int encoding_trials = 0;
					do {
					if (!budget.spend((1 << n) * (end - begin) + GetSize(classes) * bridge_count)) return;
					std::vector<int> bridges;
					for (int bit = 0; bit < bridge_count; bit++) {
						std::vector<Cube> cubes;
						for (int b = 0; b < GetSize(classes); b++) { Const pattern(State::Sa, vars.back() + 1); for (int i = 0; i < GetSize(bound); i++) pattern.set(vars[bound[i]], ((b >> i) & 1) ? State::S1 : State::S0); cubes.push_back({pattern, ((numbering[classes[b]] >> bit) & 1) ? State::S1 : State::S0}); }
						bridges.push_back(build(cubes));
					}
					if (!complete) return;
					auto candidate = roots; std::vector<int> leaves; for (auto bridge : bridges) leaves.push_back(-bridge - 1); for (int bit : free) leaves.push_back(vars[bit]);
					for (int output = begin; output < end; output++) {
						Const table(State::Sx, 1 << GetSize(leaves));
						for (int b = 0; b < GetSize(classes); b++) for (int f = 0; f < (1 << GetSize(free)); f++) {
							int row = 0; for (int i = 0; i < GetSize(bound); i++) row |= ((b >> i) & 1) << bound[i];
							bool compatible = true;
							for (int i = 0; i < GetSize(free); i++) { if (free[i] == shared && ((row >> shared) & 1) != ((f >> i) & 1)) compatible = false; row |= ((f >> i) & 1) << free[i]; }
							if (compatible) table.set(numbering[classes[b]] | (f << bridge_count), tables[output - begin][row]);
						}
						candidate[output] = add_lut(leaves, table);
					}
					if (!complete) return;
					int candidate_cost = cost(candidate); if (candidate_cost < original_cost) { original_cost = candidate_cost; best_roots = std::move(candidate); }
					} while (++encoding_trials < 24 && std::next_permutation(numbering.begin(), numbering.end()));
				}
			}
			roots = std::move(best_roots);
		}
	}
	int cost(const std::vector<int> &roots) const {
		pool<int> seen;
		std::function<void(int)> visit = [&](int root) {
			if (root < 3 || seen.count(root)) return;
			seen.insert(root); for (int leaf : cut(root)) if (leaf < 0) visit(-leaf - 1);
		};
		for (auto root : roots) visit(root);
		return GetSize(seen);
	}
	SigSpec emit(Module *module, const SigSpec &inputs, const std::vector<int> &roots) const {
		dict<int, SigBit> emitted;
		std::map<std::pair<SigSpec, Const>, SigBit> functions;
		std::function<SigBit(int)> visit = [&](int root) -> SigBit {
			if (root < 3) return root == 0 ? State::S0 : root == 1 ? State::S1 : State::Sx;
			if (emitted.count(root)) return emitted.at(root);
			auto leaves = cut(root); SigSpec args; Const table;
			for (int leaf : leaves) args.append(leaf >= 0 ? inputs[leaf] : visit(-leaf - 1));
			for (int row = 0; row < (1 << GetSize(leaves)); row++) table.append(Const(eval_cut(root, leaves, row)));
			auto key = std::make_pair(args, table);
			SigBit output;
			auto cached = functions.find(key);
			if (cached != functions.end()) output = cached->second;
			else {
				Const complement = const_not(table, Const(), false, false, GetSize(table));
				auto opposite = functions.find(std::make_pair(args, complement));
				output = module->addWire(NEW_ID);
				if (opposite != functions.end()) module->addNot(NEW_ID, opposite->second, output);
				else module->addLut(NEW_ID, args, output, table);
				functions.emplace(key, output);
			}
			emitted[root] = output; return output;
		};
		SigSpec outputs; for (int root : roots) outputs.append(visit(root)); return outputs;
	}
};

struct FsmEmissionPlan {
	std::vector<FsmDag::Node> nodes;
	dict<int, FsmDag::Lut> luts;
	std::vector<int> roots;
	bool proved = false;
	int64_t capacity() const {
		int64_t bytes = int64_t(nodes.size()) * 32 + int64_t(roots.size()) * 16;
		for (auto &item : luts) bytes += 128 + int64_t(item.second.leaves.size()) * 16 + GetSize(item.second.table) * sizeof(State);
		return bytes;
	}
	bool operator==(const FsmEmissionPlan &other) const {
		if (proved != other.proved || roots != other.roots || nodes.size() != other.nodes.size() || luts.size() != other.luts.size()) return false;
		for (size_t i = 0; i < nodes.size(); i++)
			if (nodes[i].var != other.nodes[i].var || nodes[i].lo != other.nodes[i].lo || nodes[i].hi != other.nodes[i].hi) return false;
		for (auto &item : luts) {
			auto found = other.luts.find(item.first);
			if (found == other.luts.end() || item.second.leaves != found->second.leaves || item.second.table != found->second.table) return false;
		}
		return true;
	}
};

struct FsmPrefixKey {
	Design *source = nullptr;
	const std::vector<FsmModel> *models = nullptr;
	std::string configuration, construction;
	std::shared_ptr<const std::vector<std::vector<Const>>> codes;
	std::vector<FsmEmissionPlan> emissions;
	bool operator==(const FsmPrefixKey &other) const {
		return source == other.source && models == other.models && configuration == other.configuration &&
			construction == other.construction && ((!codes && !other.codes) || (codes && other.codes && *codes == *other.codes)) &&
			emissions == other.emissions;
	}
	int64_t capacity() const {
		int64_t bytes = capacity_add(sizeof(*this), capacity_add(configuration.capacity(), capacity_add(construction.capacity(),
			capacity_mul(emissions.capacity(), sizeof(FsmEmissionPlan)))));
		for (auto &emission : emissions) bytes = capacity_add(bytes, emission.capacity());
		return bytes;
	}
};

enum class TaskKind { Ordinary, Feedback };
struct FsmMappingTask {
	std::string construction;
	std::shared_ptr<const std::vector<std::vector<Const>>> codes;
	Lut4Mapping::ScriptKind script_kind;
	bool use_best = false, native = false;
	TaskKind kind = TaskKind::Ordinary;
	Lut4Mapping::ScriptKind source_script = Lut4Mapping::ScriptKind::AreaLutpack;
};

// codes 二维容量的逐元素计价；base 是各调用点自己的对象头部字节。
static int64_t codes_capacity(const std::vector<std::vector<Const>> &codes, int64_t base = 64)
{
	int64_t bytes = capacity_add(base, capacity_mul(codes.capacity(), sizeof(std::vector<Const>)));
	for (auto &encoding : codes) {
		bytes = capacity_add(bytes, capacity_mul(encoding.capacity(), sizeof(Const)));
		for (auto &code : encoding) bytes = capacity_add(bytes, capacity_mul(GetSize(code), sizeof(State)));
	}
	return bytes;
}

struct FsmGenericCheckpoint {
	std::unique_ptr<Design> design;
	FsmPrefixKey identity;
	Lut4Mapping::StructureKey source_key;
	Lut4Mapping::ScriptKind script_kind;
	bool native = false;
	std::pair<int64_t, int64_t> cost {INT64_MAX, INT64_MAX};
	int64_t metadata_capacity() const {
		int64_t result = capacity_add(sizeof(*this), capacity_add(identity.capacity(), source_key.bytes()));
		if (identity.codes) result = capacity_add(result, codes_capacity(*identity.codes));
		return result;
	}
};

static bool encoding_init(const FsmModel &model, const std::vector<Const> &codes, Const &result)
{
	result = Const(State::Sx, GetSize(codes.front()));
	if (!model.extracted) return true;
	log_assert(!model.initial.empty()); result = codes.at(model.initial.front());
	for (int state : model.initial) for (int bit = 0; bit < GetSize(result); bit++) if (result[bit] != codes.at(state)[bit]) result.set(bit, State::Sx);
	int unknown = 0; for (auto bit : result) if (bit == State::Sx) unknown++;
	if ((uint64_t(1) << unknown) != model.initial.size()) return false;
	// 编码唯一且集合大小相同，因此公共位表示的代码空间恰好等于初始集合。
	pool<Const> unique; for (int state : model.initial) unique.insert(codes.at(state));
	return GetSize(unique) == GetSize(model.initial);
}

static std::vector<Const> numbered(const std::vector<int> &order, int width)
{
	std::vector<Const> result(order.size());
	for (int i = 0; i < GetSize(order); i++) result.at(order[i]) = Const(i ^ (i >> 1), width);
	return result;
}

struct FsmPlan { std::vector<Const> codes; int cost = 0; };

static std::vector<FsmPlan> plans_for(const FsmModel &model, FsmLimits &budget)
{
	FsmStorage storage(budget);
	if (!storage.reserve(int64_t(GetSize(model.data.transition_table)) * (256 + 4 * (model.data.num_inputs + model.data.num_outputs)) + 8 * budget.states * budget.states)) return {};
	int n = GetSize(model.data.state_table), width = 1; while ((uint64_t(1) << width) < uint64_t(n)) width++;
	std::vector<FsmPlan> result;
	auto consider = [&](const std::vector<Const> &codes) {
		if (GetSize(codes.front()) > model.width_limit) return;
		Const init; if (!encoding_init(model, codes, init)) return;
		for (auto &plan : result) if (plan.codes == codes) return;
		FsmDag dag(budget); auto roots = dag.functions(model, codes);
		if (dag.complete) dag.decompose(roots);
		if (dag.complete && storage.reserve(128 + GetSize(codes) * (64 + GetSize(codes.front())))) result.push_back({codes, dag.cost(roots)});
	};
	consider(model.data.state_table);
	std::vector<int> order(n); std::iota(order.begin(), order.end(), 0);
	std::vector<Const> binary; for (int i = 0; i < n; i++) binary.push_back(Const(i, width)); consider(binary);
	std::vector<std::vector<std::pair<Const, Const>>> signatures(n);
	std::vector<std::vector<int>> adjacency(n, std::vector<int>(n));
	for (auto &tr : model.data.transition_table) {
		if (tr.state_in < 0 || tr.state_out < 0) return result;
		signatures.at(tr.state_in).emplace_back(tr.ctrl_in, tr.ctrl_out);
		adjacency.at(tr.state_in).at(tr.state_out)++; adjacency.at(tr.state_out).at(tr.state_in)++;
	}
	for (auto &signature : signatures) std::sort(signature.begin(), signature.end());
	std::map<Const, std::vector<const FsmData::transition_t *>> cube_groups;
	for (auto &tr : model.data.transition_table) cube_groups[tr.ctrl_in].push_back(&tr);
	auto similarities = [&]() {
	for (auto &group : cube_groups) for (auto left : group.second) for (auto right : group.second) {
		if (!budget.spend(model.data.num_outputs + 4)) return;
		if (left->state_in == right->state_in) continue;
		int score = left->state_out == right->state_out ? 4 : 0;
		if (signatures[left->state_out] == signatures[right->state_out]) score += 2;
		if ((left->state_in == left->state_out) == (right->state_in == right->state_out)) score++;
		for (int bit = 0; bit < model.data.num_outputs; bit++) if (left->ctrl_out[bit] == right->ctrl_out[bit]) score++;
		adjacency[left->state_in][right->state_in] += score;
	}
	}; similarities();
	std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return signatures[a] < signatures[b]; }); consider(numbered(order, width));
	std::vector<std::vector<int>> groups;
	for (int state : order) {
		if (groups.empty() || signatures[groups.back().front()] != signatures[state]) groups.push_back({});
		groups.back().push_back(state);
	}
	int group_bits = 0, member_bits = 0, largest = 0;
	while ((1 << group_bits) < GetSize(groups)) group_bits++;
	for (auto &group : groups) largest = std::max(largest, GetSize(group));
	while ((1 << member_bits) < largest) member_bits++;
	if (group_bits + member_bits <= model.width_limit) {
		std::vector<Const> grouped(n);
		for (int group = 0; group < GetSize(groups); group++) for (int member = 0; member < GetSize(groups[group]); member++)
			grouped[groups[group][member]] = Const(group | (member << group_bits), std::max(1, group_bits + member_bits));
		consider(grouped);
	}
	std::vector<int> neighbors; pool<int> used;
	for (int i = 0; i < n; i++) {
		int best = -1, score = -1;
		for (int state = 0; state < n; state++) if (!used.count(state)) {
			int value = neighbors.empty() ? 0 : adjacency[neighbors.back()][state];
			if (!neighbors.empty() && signatures[neighbors.back()] == signatures[state]) value += n;
			if (value > score) { score = value; best = state; }
		}
		neighbors.push_back(best); used.insert(best);
	}
	consider(numbered(neighbors, width));
	if (!result.empty()) {
		auto best = *std::min_element(result.begin(), result.end(), [](const FsmPlan &a, const FsmPlan &b) { return a.cost < b.cost; });
		int trials = 0;
		for (int a = 0; a < n && trials < 24; a++) for (int b = a + 1; b < n && trials < 24; b++, trials++) {
			auto codes = best.codes; std::swap(codes[a], codes[b]); consider(codes);
			if (result.back().cost < best.cost) best = result.back();
		}
	}
	return result;
}

// 检查每个状态关系下的全部控制取值，同时保存原输出定义程度。
struct FsmProofLogic {
	Module *module;
	pool<IdString> cells, wires;
	FsmProofLogic(Module *module) : module(module) {
		for (auto cell : module->cells()) cells.insert(cell->name);
		for (auto wire : module->wires()) wires.insert(wire->name);
	}
	~FsmProofLogic() {
		std::vector<Cell *> remove_cells; for (auto cell : module->cells()) if (!cells.count(cell->name)) remove_cells.push_back(cell);
		for (auto cell : remove_cells) module->remove(cell);
		pool<Wire *> remove_wires; for (auto wire : module->wires()) if (!wires.count(wire->name)) remove_wires.insert(wire);
		module->remove(remove_wires);
	}
};

static FsmProofResult prove_model(Module *module, const FsmModel &model, const FfData &old_ff,
		const SigSpec &new_q, const SigSpec &new_d, const SigSpec &new_outputs, const std::vector<Const> &codes,
		const pool<Cell *> &generated, FsmLimits &budget)
{
	SigMap sigmap(module); ezMiniSAT ez; SatGen sat(&ez, &sigmap); sat.model_undef = true;
	FsmStorage storage(budget);
	if (!storage.reserve(int64_t(module->cells_size()) * 512)) return {FsmProofStatus::LimitReached, budget.limit_reason};
	FsmIndex index(module);
	pool<Cell *> imported, visiting;
	int cells = 0;
	FsmProofResult import_result {FsmProofStatus::Proved, "SAT cone imported"};
	std::function<bool(SigSpec)> import = [&](SigSpec sig) {
		for (auto bit : sigmap(sig)) if (bit.wire && index.drivers.count(bit)) {
			if (GetSize(index.drivers.at(bit)) != 1)
				log_error("opt_fsm_lut4: multiple drivers in state proof for %s.%s.\n", log_id(model.module), log_id(model.cell));
			auto cell = *index.drivers.at(bit).begin();
			if (StaticCellTypes::categories.is_ff(cell->type) || cell->type == ID($fsm) || imported.count(cell)) continue;
			if (visiting.count(cell))
				log_error("opt_fsm_lut4: combinational cycle in state proof at %s.%s.\n", log_id(module), log_id(cell));
			if (++cells > budget.nodes) { import_result = {FsmProofStatus::LimitReached, "SAT cone node allowance"}; return false; }
			if (!budget.spend(64) || !storage.reserve(4096)) { import_result = {FsmProofStatus::LimitReached, budget.limit_reason}; return false; }
			visiting.insert(cell);
			for (auto &port : cell->connections()) if (index.types.cell_input(cell->type, port.first) && !import(port.second)) return false;
			if (!sat.importCell(cell)) {
				if (generated.count(cell))
					log_error("opt_fsm_lut4: generated candidate cell cannot be imported into SAT: %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
				log("opt_fsm_lut4: unsupported source proof cell %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
				import_result = {FsmProofStatus::Unsupported, "source cell has no SAT model"}; return false;
			}
			visiting.erase(cell); imported.insert(cell);
		}
		return true;
	};
	if (!import(old_ff.sig_d) || !import(new_d) || !import(load_signal(module, model.saved_outputs)) || !import(new_outputs)) return import_result;
	// fsm_map 只比较状态模式中指定的位；其余位保持全部允许取值。
	auto matches = [&](SigSpec signal, const Const &pattern) {
		log_assert(GetSize(signal) == GetSize(pattern));
		int result = ez.CONST_TRUE;
		for (int bit = 0; bit < GetSize(pattern); bit++) if (pattern[bit] == State::S0 || pattern[bit] == State::S1)
			result = ez.AND(result, sat.signals_eq(signal[bit], SigBit(pattern[bit])));
		return result;
	};
	auto relation = [&](SigSpec original, SigSpec candidate) {
		int result = ez.CONST_FALSE;
		for (int state = 0; state < GetSize(codes); state++)
			result = ez.OR(result, ez.AND(matches(original, model.data.state_table[state]), matches(candidate, codes[state])));
		return result;
	};
	ez.assume(ez.vec_reduce_and(ez.vec_not(sat.importUndefSigSpec(old_ff.sig_q))));
	ez.assume(ez.vec_reduce_and(ez.vec_not(sat.importUndefSigSpec(new_q))));
	ez.assume(relation(old_ff.sig_q, new_q));
	int binary_inputs = ez.vec_reduce_and(ez.vec_not(sat.importUndefSigSpec(load_signal(module, model.saved_inputs))));
	int mismatch = ez.AND(binary_inputs, ez.NOT(relation(old_ff.sig_d, new_d)));
	// 原状态模式的自由位不参与 D 比较；指定的位保持未定义值细化约束。
	FsmProofLogic temporary(module);
	FsmDag decode(budget); std::vector<int> roots;
	for (int bit = 0; bit < model.data.state_bits; bit++) {
		std::vector<FsmDag::Cube> values, cares;
		for (int state = 0; state < GetSize(codes); state++) {
			auto value = model.data.state_table[state][bit];
			bool care = value == State::S0 || value == State::S1;
			values.push_back({codes[state], care ? value : State::Sx});
			cares.push_back({codes[state], care ? State::S1 : State::S0});
		}
		roots.push_back(decode.build(values)); roots.push_back(decode.build(cares));
	}
	if (!decode.complete) return decode.failure();
	auto decoded = decode.emit(module, new_d, roots);
	for (auto cell : module->cells()) if (!temporary.cells.count(cell->name) && !sat.importCell(cell))
		log_error("opt_fsm_lut4: generated decoder cell cannot be imported into SAT: %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
	for (int bit = 0; bit < model.data.state_bits; bit++) {
		int original = sat.importSigBit(old_ff.sig_d[bit]), candidate = sat.importSigBit(decoded[2 * bit]);
		int old_undef = sat.importUndefSigBit(old_ff.sig_d[bit]), new_undef = sat.importUndefSigBit(decoded[2 * bit]);
		int care = sat.importSigBit(decoded[2 * bit + 1]), care_undef = sat.importUndefSigBit(decoded[2 * bit + 1]);
		mismatch = ez.OR(mismatch, ez.AND(ez.NOT(old_undef), ez.NOT(care_undef), care, ez.OR(new_undef, ez.XOR(original, candidate))));
	}
	SigSpec old_values = load_signal(module, model.saved_outputs), new_values = new_outputs;
	for (int bit = 0; bit < GetSize(old_values); bit++) {
		int original = sat.importSigBit(old_values[bit]), candidate = sat.importSigBit(new_values[bit]);
		int old_undef = sat.importUndefSigBit(old_values[bit]), new_undef = sat.importUndefSigBit(new_values[bit]);
		mismatch = ez.OR(mismatch, ez.AND(ez.NOT(old_undef), ez.OR(new_undef, ez.XOR(original, candidate))));
	}
	ez.bind(mismatch);
	int64_t cap = std::min<int64_t>(budget.sat, 200000);
	if (cap <= 0) return {FsmProofStatus::LimitReached, "SAT propagation allowance"};
	if (!budget.spend(ez.numCnfVariables() + 1)) return {FsmProofStatus::LimitReached, budget.limit_reason};
	ez.setSolverPropLimit(cap);
	if (!budget.time_available()) return {FsmProofStatus::LimitReached, "coordinator deadline"};
	bool counterexample = ez.solve(mismatch); budget.sat -= std::min<int64_t>(budget.sat, ez.getSolverProps());
	if (counterexample) return {FsmProofStatus::Disproved, "SAT counterexample to candidate state relation"};
	if (ez.getSolverPropLimitStatus()) return {FsmProofStatus::LimitReached, "SAT propagation allowance"};
	log("opt_fsm_lut4: state relation proved for %s.%s.\n", log_id(model.module), log_id(model.cell));
	return {FsmProofStatus::Proved, "state relation UNSAT"};
}

static FsmProofResult apply_model(Design *design, const FsmModel &model, const std::vector<Const> &codes, FsmLimits &budget,
		FsmEmissionPlan &emission, FsmStorage &emission_storage, const FsmEmissionPlan *fixed = nullptr)
{
	Module *module = design->module(model.module); Cell *cell = module->cell(model.cell);
	if (!cell && !model.extracted) for (auto item : module->cells()) if (item->type == ID($fsm) && item->getParam(ID::NAME).decode_string() == model.fsm_name) { log_assert(!cell); cell = item; }
	log_assert(cell);
	SigMap sigmap(module); FfInitVals initvals(&sigmap, module);
	FfData old_ff;
	std::vector<IdString> reference_cells;
	if (!model.extracted) {
		pool<Cell *> before; for (auto item : module->cells()) before.insert(item);
		RTLIL::Selection selection(false); selection.select(module, cell);
		Pass::call_on_selection(design, selection, "fsm_map");
		for (auto item : module->cells()) if (!before.count(item)) {
			if (StaticCellTypes::categories.is_ff(item->type)) old_ff = FfData(&initvals, item);
			else reference_cells.push_back(item->name);
		}
		log_assert(old_ff.cell);
	} else old_ff = FfData(&initvals, cell);
	FsmDag dag(budget); std::vector<int> roots;
	if (fixed) {
		log_assert(fixed->proved);
		if (!dag.storage.reserve(fixed->capacity())) return {FsmProofStatus::LimitReached, budget.limit_reason};
		dag.nodes = fixed->nodes; dag.luts = fixed->luts; roots = fixed->roots;
	} else {
		roots = dag.functions(model, codes); if (dag.complete) dag.decompose(roots); if (!dag.complete) return dag.failure();
	}
	pool<Cell *> source_cells; for (auto item : module->cells()) source_cells.insert(item);
	auto new_q = module->addWire(NEW_ID, GetSize(codes.front())); new_q->attributes[ID::fsm_encoding] = Const("none");
	SigSpec args = SigSpec(new_q); args.append(load_signal(module, model.saved_inputs));
	auto values = dag.emit(module, args, roots);
	auto new_d = values.extract(0, new_q->width), outputs = values.extract(new_q->width, model.data.num_outputs);
	pool<Cell *> generated; for (auto item : module->cells()) if (!source_cells.count(item)) generated.insert(item);
	// fixed 来自相同入口设计已经证明的完整发射计划。
	FsmProofResult proof {FsmProofStatus::Proved, "reused proved emission from identical source and encoding"};
	if (!fixed) proof = prove_model(module, model, old_ff, new_q, new_d, outputs, codes, generated, budget);
	if (!proof.proved()) return proof;
	int64_t emission_bytes = int64_t(dag.nodes.size()) * 32 + int64_t(roots.size()) * 16;
	for (auto &item : dag.luts) emission_bytes += 128 + int64_t(item.second.leaves.size()) * 16 + GetSize(item.second.table) * sizeof(State);
	if (!emission_storage.reserve(emission_bytes)) return {FsmProofStatus::LimitReached, budget.limit_reason};
	emission.nodes = dag.nodes; emission.luts = dag.luts; emission.roots = roots;
	FfData ff = old_ff; ff.name = NEW_ID; ff.cell = nullptr;
	Const init; if (!encoding_init(model, codes, init)) return {FsmProofStatus::Disproved, "encoding does not preserve the initial state set"};
	ff.sig_q = new_q; ff.sig_d = new_d; ff.width = new_q->width; ff.val_init = init;
	if (ff.has_arst) {
		int state = model.extracted ? -1 : model.data.reset_state;
		if (model.extracted) for (int i = 0; i < GetSize(model.data.state_table); i++) if (model.data.state_table[i] == ff.val_arst) state = i;
		if (state < 0) log_error("opt_fsm_lut4: asynchronous reset state missing from model %s.%s.\n", log_id(model.module), log_id(model.cell));
		ff.val_arst = codes.at(state);
	}
	if (ff.has_srst) {
		int state = -1; for (int i = 0; i < GetSize(model.data.state_table); i++) if (model.data.state_table[i] == ff.val_srst) state = i;
		if (state < 0) log_error("opt_fsm_lut4: synchronous reset state missing from model %s.%s.\n", log_id(model.module), log_id(model.cell));
		ff.val_srst = codes.at(state);
	}
	old_ff.remove();
	for (auto name : reference_cells) { auto item = module->cell(name); log_assert(item); module->remove(item); }
	for (auto name : model.removed) { auto item = module->cell(name); log_assert(item); module->remove(item); }
	module->connect(load_signal(module, model.saved_outputs), outputs); ff.emit();
	emission.proved = true;
	return proof;
}

static std::pair<int64_t, int64_t> metrics(Design *design)
{
	pool<IdString> visiting;
	dict<IdString, std::pair<int64_t, int64_t>> cache;
	std::function<std::pair<int64_t, int64_t>(Module *)> count = [&](Module *module) {
		if (cache.count(module->name)) return cache.at(module->name);
		log_assert(!visiting.count(module->name)); visiting.insert(module->name);
		int64_t area = 0, flops = 0;
		for (auto cell : module->cells()) {
			log_assert(cell->type != ID($lut));
			auto child = design->module(cell->type);
			if (child && !child->get_bool_attribute(ID::blackbox) && !child->get_bool_attribute(ID::whitebox)) {
				auto cost = count(child);
				log_assert(cost.first <= INT64_MAX - area && cost.second <= INT64_MAX - flops);
				area += cost.first; flops += cost.second;
			} else {
				if (cell->type.in(ID(cycloneiv_lcell_comb), ID($not), ID($_NOT_))) area++;
				if (cell->type == ID(dffeas)) flops++;
			}
		}
		visiting.erase(module->name);
		return cache[module->name] = std::make_pair(area, flops);
	};
	auto top = design->top_module(); log_assert(top);
	return count(top);
}

struct OptFsmLut4Pass : Pass {
	OptFsmLut4Pass() : Pass("opt_fsm_lut4", "search FSM encodings with complete Cyclone IV mapping") {}
	void help() override {
		log("\n    opt_fsm_lut4 -family cycloneiv [options]\n\n");
		log("Complete the normal mapping before FSM analysis, then jointly compare FSM\n");
		log("reconstruction, generic/native arithmetic and ABC9 scripts with the full tail.\n");
		log("Native carry is compared through complete Cyclone IV mapping candidates.\n");
		log("Keep strictly smaller LUT4 area with DFF count at most the generic baseline.\n");
		log("    -max-states <n>          default 64\n");
		log("    -max-initial-states <n>  default 256\n");
		log("    -max-transitions <n>     default 4096\n");
		log("    -max-nodes <n>           default 8192\n");
		log("    -max-work <n>            FSM analysis/encoding/proof work, default 8000000\n");
		log("    -max-mapping-work <n>    lower the mapping limit of 16 times baseline proxy\n");
		log("    -max-mappings <n>        1..8, default 8, including the original implementation\n");
		log("    -max-memory <MiB>        optional search reservation limit, 1..4096\n");
		log("Default memory is calibrated once after baseline: C=max(S,B,phase_C),\n");
		log("phase_C includes observed candidate capacities throughout baseline; L=live\n");
		log("source/baseline/metadata excluding prefix, W=max(J+16MiB,\n");
		log("P_resyn+64MiB,P_resub+32MiB,A+H), H=observed map/unmap/holes peaks,\n");
		log("G=min(16MiB,max(1MiB,(S+B)/8)), R=self peak RSS bytes.\n");
		log("E=min(2*R,max(64MiB,2*C+W+G)); limit=min(1024MiB,max(64MiB,L+E)).\n");
		log("Explicit memory overrides that search limit; required baseline/transfer\n");
		log("continue with reported overage. Local search limits remain unchanged.\n");
		log("Mapping proxy reservations use area/cascade/rewrite/expanded/feedback factors 1/3/1.5/2/2.\n");
		log("    -feedback               enable one generation of generic LUT feedback\n");
		log("        Disabled by default; requires combinational mapping without -dff.\n");
		log("        Capture complete generic checkpoints paired with eligible DFF results.\n");
		log("        Feedback follows the first completed structural candidate or precedes\n");
		log("        an ordinary generic script-only variation, sharing all eight mapping slots.\n");
		log("All search shares a deadline of the measured generic baseline full tail\n");
		log("plus max(0,8*suffix_core-common_Mux_seconds). Suffix core excludes\n");
		log("prefix/capture/clone management; common Mux uses this synth invocation.\n");
		log("A standalone coordinator has zero common Mux time.\n");
		log("Postprocessing keeps its own work, SAT and workspace limits.\n");
		log("    -nobram -nodsp -dff -iopads -noflatten\n");
		log("        preserve the corresponding synth_intel options\n\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		std::unique_ptr<MuxResourceScope> mux_scope;
		if (!design->scratchpad.count("muxledger.scope")) mux_scope.reset(new MuxResourceScope(design));
		FsmLimits budget; std::string family, options; size_t argidx;
		bool feedback_enabled = false;
		int64_t mapping_work_limit = INT64_MAX, explicit_memory = 0;
		for (argidx = 1; argidx < args.size(); argidx++) {
			auto arg = args[argidx];
			if (arg == "-family" && argidx + 1 < args.size()) { family = args[++argidx]; continue; }
			if (arg == "-feedback") { feedback_enabled = true; continue; }
			if (arg == "-nobram" || arg == "-nodsp" || arg == "-dff" || arg == "-iopads" || arg == "-noflatten") { options += " " + arg; continue; }
			if (argidx + 1 < args.size() && (arg == "-max-states" || arg == "-max-initial-states" || arg == "-max-transitions" || arg == "-max-nodes" || arg == "-max-work" || arg == "-max-mappings" || arg == "-max-mapping-work" || arg == "-max-memory")) {
				int64_t value = 0; auto &text = args[++argidx]; auto parsed = std::from_chars(text.data(), text.data() + text.size(), value);
				if (parsed.ec != std::errc() || parsed.ptr != text.data() + text.size() || value < 1) log_cmd_error("opt_fsm_lut4: invalid positive integer.\n");
				if (arg != "-max-work" && arg != "-max-mapping-work" && value > INT_MAX) log_cmd_error("opt_fsm_lut4: integer exceeds supported range.\n");
				if (arg == "-max-states") budget.states = value;
				if (arg == "-max-initial-states") budget.initials = value;
				if (arg == "-max-transitions") budget.transitions = value;
				if (arg == "-max-nodes") budget.nodes = value;
				if (arg == "-max-work") budget.analysis_work = value;
				if (arg == "-max-mapping-work") mapping_work_limit = value;
				if (arg == "-max-mappings") budget.mappings = value;
				if (arg == "-max-memory") {
					if (value > 4096) log_cmd_error("opt_fsm_lut4: -max-memory must be 1..4096 MiB.\n");
					explicit_memory = capacity_mul(value, 1048576); budget.memory = explicit_memory;
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (family != "cycloneiv" || !design->full_selection()) log_cmd_error("opt_fsm_lut4 requires -family cycloneiv and a fully selected design.\n");
		if (design->scratchpad_get_bool("opt_fsm_lut4.evaluating")) log_cmd_error("opt_fsm_lut4: recursive search.\n");
		if (budget.states > 256 || budget.initials > 4096 || budget.nodes > 65536 || budget.mappings > Lut4Mapping::max_full_mappings) log_cmd_error("opt_fsm_lut4: resource limit outside supported range.\n");
		log_header(design, "Executing OPT_FSM_LUT4 pass.\n");
		log("opt_fsm_lut4: mapping resource limits mappings=%d maximum=%d baseline proxy factor=16 optional suffix factor=8 automatic memory cap=1073741824 bytes post work caps=16000000/100000000 SAT=4000000 post workspace=67108864/33554432 bytes mapping work override=%lld memory override=%lld bytes.\n",
			budget.mappings, Lut4Mapping::max_full_mappings, (long long)mapping_work_limit, (long long)explicit_memory);
		bool sequential = options.find(" -dff") != std::string::npos;
		if (feedback_enabled && sequential) log_cmd_error("opt_fsm_lut4: -feedback requires mapping without -dff.\n");
		for (auto module : design->selected_modules())
			if (module->has_processes()) log_cmd_error("opt_fsm_lut4: run proc before complete mapping.\n");
		int64_t source_cells = 0, source_wires = 0;
		for (auto module : design->selected_modules()) {
			source_cells = capacity_add(source_cells, module->cells_size());
			for (auto wire : module->wires()) source_wires = capacity_add(source_wires, wire->width);
		}
		// 跳过与 feedback 统计只在 complete() 的日志里读取一次，收拢为局部结构体。
		struct FsmSkipStats { int work = 0, memory = 0, cascade_work = 0, deadline = 0; } skipped;
		double complete_mapping_seconds = 0, incomplete_mapping_seconds = 0;
		std::array<double, Lut4Mapping::script_kind_count> core_estimates {};
		std::array<double, Lut4Mapping::script_kind_count> suffix_estimates {};
		FsmLimits::Clock::duration last_mapping_duration {};
		FsmLimits::Clock::duration last_prefix_duration {}, last_capture_duration {};
		FsmLimits::Clock::duration last_abc_duration {}, last_cell_tail_duration {}, last_post_setup_duration {};
		int64_t baseline_module_capacity = 0;
		int64_t source_capacity = design_capacity(design, &baseline_module_capacity);
		int64_t baseline_phase_capacity = source_capacity;
		std::array<int64_t, 3> baseline_helper_capacity {{0, 0, 0}};
		FsmStorage design_storage(budget);
		design_storage.reserve_required(capacity_mul(2, source_capacity));
		Lut4Mapping::PostContext post(budget, "cycloneiv" + options);
		post.budget.carry_enabled = !sequential;
		FsmStorage prefix_storage(budget);
		FsmStorage generic_storage(budget), pending_storage(budget);
		std::unique_ptr<FsmGenericCheckpoint> best_eligible_generic, pending_generic;
		using Task = FsmMappingTask;
		Task best_task {"normal", {}, Lut4Mapping::ScriptKind::AreaLutpack};
		std::vector<FsmEmissionPlan> best_emissions;
		FsmStorage best_emission_storage(budget);
		bool feedback_attempted = false, optional_completed = false;
		struct FsmFeedbackStats {
			int captures = 0, mappings = 0, abc_executions = 0;
			int64_t capture_work = 0, checkpoint_peak = 0, work = 0, resyn_work = 0, resub_work = 0, sat_work = 0;
			double capture_seconds = 0, seconds = 0;
		} feedback_stats;
		auto clear_pending = [&]() { pending_generic.reset(); pending_storage.resize_required(0); };
		auto complete_generic = [&](const std::pair<int64_t, int64_t> &cost, int64_t maximum_dff) {
			if (!pending_generic) return;
			pending_generic->cost = cost;
			if (cost.second <= maximum_dff && (!best_eligible_generic || cost.first < best_eligible_generic->cost.first)) {
				best_eligible_generic = std::move(pending_generic);
				generic_storage.resize_required(0);
				int64_t bytes = pending_storage.bytes; pending_storage.resize_required(0); generic_storage.resize_required(bytes);
				log_debug("opt_fsm_lut4: eligible generic checkpoint construction=%s script=%s carry_mode=%s complete LUT4=%lld DFF=%lld capacity=%lld bytes.\n",
					best_eligible_generic->identity.construction, Lut4Mapping::script_name(best_eligible_generic->script_kind),
					best_eligible_generic->native ? "native" : "generic",
					(long long)cost.first, (long long)cost.second, (long long)generic_storage.bytes);
			} else clear_pending();
		};
		std::unique_ptr<Design> prefix_cache;
		FsmPrefixKey prefix_key;
		double prefix_seconds = 0, prefix_clone_seconds = 0;
		auto evict_prefix = [&](const char *reason) {
			if (!prefix_cache) return;
			log_debug("opt_fsm_lut4: prefix cache evict construction=%s reason=%s capacity=%lld bytes.\n",
				prefix_key.construction, reason, (long long)prefix_storage.bytes);
			prefix_cache.reset(); prefix_key = {}; prefix_storage.resize_required(0);
		};
		budget.reclaim_memory = [&]() { evict_prefix("workspace admission"); };
		auto prefix_proxy = [](int64_t capacity) { return capacity_add(1024, capacity / 16); };
		bool last_mapping_success = false;
		std::pair<int64_t, int64_t> candidate_cost;
		auto map = [&](Design *candidate, Lut4Mapping::ScriptKind script_kind, const std::string &construction, bool native,
			const FsmPrefixKey &key, bool reuse, FsmStorage &storage, int64_t workspace, bool baseline_mapping = false,
			FsmLimits::Clock::duration reuse_duration = FsmLimits::Clock::duration::zero(),
			bool feedback = false) -> Lut4Mapping::AuditResult {
			auto start = std::chrono::steady_clock::now() - reuse_duration;
			last_mapping_success = false;
			clear_pending();
			FsmStorage phase_storage(budget), post_clone_storage(budget);
			Lut4Mapping::MappingPhase active_phase = Lut4Mapping::MappingPhase::Idle;
			FsmLimits::Clock::time_point abc_started {}, abc_finished {};
			last_abc_duration = {}; last_cell_tail_duration = {}; last_post_setup_duration = {};
			int64_t abc_external = workspace, abc_prepaid_clone = 0, abc_prepaid_helpers = 0, abc_saved_peak = 0, abc_helper_peak = 0;
			int64_t abc_resident_floor = 0;
			std::array<int64_t, 3> helper_prepaid {{0, 0, 0}}, helper_peak {{0, 0, 0}};
			// 无状态局部统计：调用方在需要的位置读取当前Design容量与modules分量。
			auto settle_design = [&](int64_t actual, int64_t modules) {
				if (baseline_mapping) {
					baseline_phase_capacity = std::max(baseline_phase_capacity, actual);
					baseline_module_capacity = std::max(baseline_module_capacity, modules);
				}
				// stash/load 期间继续覆盖当前 Design 接收的一份 modules。
				storage.resize_required(capacity_add(std::max(actual, abc_resident_floor), baseline_mapping ? source_capacity : 0));
			};
			Lut4Mapping::PhaseContext phase_context(candidate, [&](Lut4Mapping::MappingPhase phase) {
				if (active_phase == Lut4Mapping::MappingPhase::Abc && phase != active_phase) {
					abc_finished = FsmLimits::Clock::now(); last_abc_duration = abc_finished - abc_started;
				}
				if (phase == Lut4Mapping::MappingPhase::Abc && active_phase != phase) abc_started = FsmLimits::Clock::now();
				phase_storage.resize_required(0); active_phase = phase;
				// phase进入时同一基本块取得本次actual/modules，供resident floor、baseline与storage结算复用。
				int64_t entry_modules = 0;
				int64_t entry_actual = design_capacity(candidate, &entry_modules);
				abc_resident_floor = phase == Lut4Mapping::MappingPhase::Abc ? entry_actual : 0;
				settle_design(entry_actual, entry_modules);
				bool construction_phase = phase == Lut4Mapping::MappingPhase::Prefix || phase == Lut4Mapping::MappingPhase::Arithmetic || phase == Lut4Mapping::MappingPhase::Abc;
				if (!baseline_mapping && construction_phase && !budget.time_available()) {
					budget.set_limit(FsmLimitKind::Deadline, "coordinator deadline"); return false;
				}
				int64_t amount = 0;
				if (phase == Lut4Mapping::MappingPhase::Prefix) amount = capacity_add(mux_index_capacity(candidate), 16 * 1048576);
				if (phase == Lut4Mapping::MappingPhase::Abc) {
					abc_prepaid_clone = abc_clone_capacity(candidate);
					helper_prepaid = abc_helper_capacity(candidate, sequential);
					for (size_t index = 0; index < helper_prepaid.size(); ++index) {
						helper_prepaid[index] = std::max(helper_prepaid[index], baseline_helper_capacity[index]);
						abc_prepaid_helpers = capacity_add(abc_prepaid_helpers, helper_prepaid[index]);
					}
					amount = capacity_add(abc_prepaid_clone, capacity_add(abc_prepaid_helpers, abc_external));
					log_debug("opt_fsm_lut4: ABC prepaid clone=%lld helpers=%lld map=%lld unmap=%lld holes=%lld external=%lld bytes.\n",
						(long long)abc_prepaid_clone, (long long)abc_prepaid_helpers, (long long)helper_prepaid[0],
						(long long)helper_prepaid[1], (long long)helper_prepaid[2], (long long)abc_external);
				}
				bool carry_phase = phase == Lut4Mapping::MappingPhase::Carry;
				bool post_phase = phase == Lut4Mapping::MappingPhase::Resyn || phase == Lut4Mapping::MappingPhase::Resub || carry_phase;
				bool lookup_phase = phase == Lut4Mapping::MappingPhase::Lookup;
				if (lookup_phase) {
					int64_t graph = 0;
					for (auto &entry : Lut4Mapping::post_modules(candidate)) {
						auto module = entry.second;
						graph = capacity_add(graph, capacity_add(capacity_mul(module->cells_size(), 512), capacity_mul(module->wires_size(), 256)));
						for (auto wire : module->wires()) graph = capacity_add(graph, capacity_mul(wire->width, 128));
					}
					amount = std::max(graph, post_capacity(candidate, true));
					if (!baseline_mapping) amount = std::min(amount, std::max<int64_t>(0, budget.memory - budget.bytes));
				}
				int64_t post_index_request = 0, post_workspace_limit = 0, post_available = 0, post_workspace_request = 0;
				if (post_phase) {
					bool resyn = phase == Lut4Mapping::MappingPhase::Resyn;
					if (carry_phase) post.budget.lut_scale = Lut4Mapping::carry_scale(candidate);
					bool carry_search = !carry_phase || post.budget.carry_allowance() > 0;
					post_index_request = carry_phase ? (carry_search ? carry_capacity(candidate) : 0) : post_capacity(candidate, resyn);
					post_workspace_limit = carry_phase ? (carry_search ? carry_workspace_limit(candidate, post_index_request) : 0) :
						resyn ? Lut4Mapping::post_resyn_workspace : Lut4Mapping::post_resub_workspace;
					post_available = std::max<int64_t>(0, budget.memory - budget.bytes);
					amount = post_phase_capacity(post_index_request, post_workspace_limit, post_available, baseline_mapping);
					post_workspace_request = amount - post_index_request;
				}
				bool post_deadline = !baseline_mapping && (post_phase || lookup_phase) && !budget.time_available();
				if (post_deadline) amount = 0;
				if (post_phase)
					log_debug("opt_fsm_lut4: post phase reservation stage=%s baseline=%d index=%lld workspace cap=%lld available=%lld workspace=%lld request=%lld deadline=%d bytes.\n",
						Lut4Mapping::phase_name(phase), baseline_mapping, (long long)post_index_request, (long long)post_workspace_limit,
						(long long)post_available, (long long)post_workspace_request, (long long)amount, post_deadline);
				bool admitted = true;
				if (baseline_mapping) phase_storage.reserve_required(amount);
				else if (!phase_storage.reserve(amount)) admitted = false;
				auto context = Lut4Mapping::PhaseContext::active();
				context->post_credit = post_phase || lookup_phase ? phase_storage.bytes : 0;
				if (post_phase) post.publish(candidate);
				if (post_deadline) candidate->scratchpad_set_string("opt_lut4_post.memory_remaining", "0");
				log_debug("opt_fsm_lut4: mapping phase=%s construction=%s resident=%lld phase request=%lld phase reservation=%lld total=%lld memory=%lld admitted=%d required_overage=%lld bytes.\n",
					Lut4Mapping::phase_name(phase), construction, (long long)storage.bytes, (long long)amount, (long long)phase_storage.bytes, (long long)budget.bytes,
					(long long)budget.memory, admitted, (long long)(baseline_mapping ? std::max<int64_t>(0, budget.bytes - budget.memory) : 0));
				return admitted;
			}, [&]() {
				// observe位置重新读取当前Design，同一基本块取得容量与modules分量。
				int64_t observed_modules = 0;
				int64_t observed_capacity = design_capacity(candidate, &observed_modules);
				settle_design(observed_capacity, observed_modules);
				if (active_phase != Lut4Mapping::MappingPhase::Abc) return;
				int64_t saved_clone = 0, saved_modules = 0, helpers = 0, prepaid = 0;
				auto clone = saved_designs.find("$abc9");
				if (clone != saved_designs.end()) {
					// $abc9 是独立Design，使用它自己的当前容量与module分量。
					saved_clone = design_capacity(clone->second, &saved_modules);
					if (baseline_mapping) {
						baseline_phase_capacity = std::max(baseline_phase_capacity, saved_clone);
						baseline_module_capacity = std::max(baseline_module_capacity, saved_modules);
					}
				}
				size_t index = 0;
				for (const char *name : {"$abc9_map", "$abc9_unmap", "$abc9_holes"}) {
					auto found = saved_designs.find(name);
					int64_t actual = found != saved_designs.end() ? design_capacity(found->second) : 0;
					helpers = capacity_add(helpers, actual);
					helper_peak[index] = std::max(helper_peak[index], actual);
					if (baseline_mapping) baseline_helper_capacity[index] = std::max(baseline_helper_capacity[index], actual);
					prepaid = capacity_add(prepaid, std::max(actual, helper_prepaid[index]));
					++index;
				}
				abc_saved_peak = std::max(abc_saved_peak, capacity_add(saved_clone, helpers));
				abc_helper_peak = std::max(abc_helper_peak, helpers);
				int64_t amount = capacity_add(abc_external, capacity_add(std::max(saved_clone, abc_prepaid_clone), prepaid));
				if (baseline_mapping) phase_storage.resize_required(amount);
				else if (!phase_storage.resize(amount) || budget.bytes > budget.memory) {
					budget.set_limit(FsmLimitKind::Memory, "ABC clone/helper memory allowance");
					Lut4Mapping::PhaseContext::active()->failed = true;
					phase_storage.resize_required(amount);
				}
			});
			phase_context.admit_clone = [&](Design *value) { return post_clone_storage.reserve(design_capacity(value)); };
			phase_context.finish_clone = [&]() {
				// clone完成之后重新读取当前Design，同一基本块取得容量与modules分量。
				int64_t cloned_modules = 0;
				int64_t cloned_capacity = design_capacity(candidate, &cloned_modules);
				settle_design(cloned_capacity, cloned_modules);
				post_clone_storage.resize_required(0);
			};
			last_capture_duration = {}; last_prefix_duration = {};
			Lut4Mapping::clear_products(candidate);
			candidate->scratchpad_set_string("muxledger.scope", design->scratchpad_get_string("muxledger.scope"));
			post.begin(candidate, budget.completed_mappings == 0);
			candidate->scratchpad_set_bool("opt_fsm_lut4.evaluating", true);
			candidate->scratchpad_set_bool("opt_lut4_mapping.evaluating", true);
			candidate->scratchpad_set_string("opt_lut4_mapping.script_kind", Lut4Mapping::script_name(script_kind));
			candidate->scratchpad_set_string("opt_lut4_mapping.carry_mode", native ? "native" : "generic");
			log("opt_fsm_lut4: complete mapping construction=%s script=%s carry_mode=%s.\n", construction, sequential ? "sequential" : Lut4Mapping::script_name(script_kind), native ? "native" : "generic");
			Lut4Mapping::SavedDesigns saved;
			Lut4Mapping::AuditResult abc;
			std::optional<Lut4Mapping::GenericCheckpointContext> generic_context;
			if (feedback_enabled) generic_context.emplace(candidate, [&](Design *completed) {
				if (sequential || feedback || feedback_attempted || budget.completed_mappings + 1 >= budget.mappings) return;
				// 捕获位置重新读取当前Design，同一基本块取得容量与modules分量。
				int64_t captured_modules = 0;
				int64_t design_bytes = design_capacity(completed, &captured_modules), key_limit = capacity_mul(4, design_bytes);
				settle_design(design_bytes, captured_modules);
				int64_t metadata = capacity_add(key.capacity(), 4096);
				if (key.codes) metadata = capacity_add(metadata, codes_capacity(*key.codes));
				int64_t requested = capacity_add(capacity_add(design_bytes, key_limit), capacity_add(metadata, Lut4Mapping::feedback_index_capacity(completed)));
				int64_t work = capacity_mul(2, prefix_proxy(design_bytes));
				bool allowed_work = baseline_mapping ? mapping_work_limit == INT64_MAX : work <= budget.work - budget.reserved_work;
				if (!allowed_work || !budget.time_available(prefix_clone_seconds) || !pending_storage.reserve(requested)) {
					log("opt_fsm_lut4: generic capture skipped construction=%s reason=%s capacity=%lld proxy=%lld.\n", construction,
						!allowed_work ? "mapping work allowance" : !budget.time_available(prefix_clone_seconds) ? "capture deadline allowance" : "checkpoint memory allowance",
						(long long)requested, (long long)work);
					clear_pending(); return;
				}
				if (baseline_mapping) budget.actual_work = capacity_add(budget.actual_work, work);
				else log_assert(budget.spend_mapping(work));
				feedback_stats.capture_work = capacity_add(feedback_stats.capture_work, work);
				feedback_stats.checkpoint_peak = std::max(feedback_stats.checkpoint_peak, capacity_add(generic_storage.bytes, pending_storage.bytes));
				log("opt_fsm_lut4: generic capture charged construction=%s proxy=%lld reservation=%lld bytes.\n",
					construction, (long long)work, (long long)pending_storage.bytes);
				auto capture_started = FsmLimits::Clock::now();
				pending_generic = std::make_unique<FsmGenericCheckpoint>();
				pending_generic->identity = key;
				pending_generic->identity.source = nullptr; pending_generic->identity.models = nullptr;
				pending_generic->script_kind = script_kind; pending_generic->native = native;
				pending_generic->source_key = Lut4Mapping::mapped_structure(completed, "cycloneiv" + options, key_limit, false, true);
				if (!pending_generic->source_key.valid) {
					log("opt_fsm_lut4: generic capture skipped construction=%s reason=complete source key capacity or structure.\n", construction);
					clear_pending();
					feedback_stats.capture_seconds += std::chrono::duration<double>(FsmLimits::Clock::now() - capture_started).count();
					return;
				}
				pending_generic->design = clone_design(completed);
				int64_t actual = capacity_add(design_capacity(pending_generic->design.get()), pending_generic->metadata_capacity());
				log_assert(actual <= pending_storage.bytes); pending_storage.resize_required(actual);
				feedback_stats.captures++;
				double capture_seconds = std::chrono::duration<double>(FsmLimits::Clock::now() - capture_started).count();
				feedback_stats.capture_seconds += capture_seconds;
				log("opt_fsm_lut4: generic capture construction=%s script=%s source fields=%lld actual proxy=%lld capacity=%lld seconds=%.9f.\n",
					construction, Lut4Mapping::script_name(script_kind), (long long)pending_generic->source_key.fields.size(),
					(long long)work, (long long)actual, capture_seconds);
			});
			Lut4Mapping::PrefixContext prefix_context(candidate, [&](Design *completed, FsmLimits::Clock::duration duration) {
				last_prefix_duration = duration;
				// prefix捕获位置重新读取当前Design，同一基本块取得容量与modules分量。
				int64_t prefixed_modules = 0;
				int64_t prefixed_capacity = design_capacity(completed, &prefixed_modules);
				settle_design(prefixed_capacity, prefixed_modules);
				phase_storage.resize_required(0);
				if (budget.bytes > budget.memory) evict_prefix("active prefix capacity");
				if (sequential || budget.completed_mappings + 1 >= budget.mappings) return;
				if (prefix_cache && prefix_key == key) return;
				evict_prefix("construction identity replacement");
				int64_t capacity = capacity_add(prefixed_capacity, capacity_add(key.capacity(), 1024));
				int64_t work = prefix_proxy(prefixed_capacity);
				// 显式工作上限在校准完成后使用真实余额进行准入。
				bool work_allowed = baseline_mapping ? mapping_work_limit == INT64_MAX : work <= budget.work - budget.reserved_work;
				if (!work_allowed || capacity > budget.memory - budget.bytes) {
					log("opt_fsm_lut4: prefix cache capacity not admitted construction=%s prefix seconds=%.9f capacity=%lld bytes clone proxy=%lld reason=%s.\n",
						construction, Lut4Mapping::PostTiming::seconds(duration), (long long)capacity, (long long)work,
						work_allowed ? "memory allowance" : "mapping work allowance");
					return;
				}
				log_assert(prefix_storage.reserve(capacity));
				if (baseline_mapping) budget.actual_work += work;
				else log_assert(budget.spend_mapping(work));
				auto clone_start = FsmLimits::Clock::now();
				prefix_cache = clone_design(completed); prefix_key = key;
				last_capture_duration = FsmLimits::Clock::now() - clone_start;
				int64_t cached_capacity = design_capacity(prefix_cache.get());
				log_assert(cached_capacity + prefix_key.capacity() <= prefix_storage.bytes);
				prefix_storage.resize_required(cached_capacity + prefix_key.capacity());
				prefix_seconds = Lut4Mapping::PostTiming::seconds(duration);
				prefix_clone_seconds = Lut4Mapping::PostTiming::seconds(last_capture_duration);
				log_debug("opt_fsm_lut4: prefix cache capture construction=%s prefix seconds=%.9f clone seconds=%.9f capacity=%lld bytes clone proxy=%lld.\n",
					construction, prefix_seconds, prefix_clone_seconds, (long long)prefix_storage.bytes, (long long)work);
			});
			{
				Lut4Mapping::ScriptReference reference;
				LogManager::Scoped scoped(logger());
				auto &audit = logger().add_sink<Lut4Mapping::MappingAudit>(!sequential);
				std::unique_ptr<Lut4Mapping::FeedbackContinuation> continuation;
				if (feedback) continuation = std::make_unique<Lut4Mapping::FeedbackContinuation>(candidate);
				Pass::call(candidate, std::string("synth_intel -family cycloneiv -fsm-lut4-eval -run ") + (feedback ? "map_luts" : reuse ? "fsm_arithmetic" : "fsm_entry") + ":check" + options);
				if (phase_context.failed) {
					// failed 只由非 baseline 的准入回调置位（构造期截止检查或容量准入），baseline 永不进入本分支。
					abc = audit.finish();
					// 已完成的真实 ABC 映射继续消耗次数和工作额度。
					if (!audit.networks.empty()) {
						int64_t cells = 0;
						for (auto module : candidate->selected_modules()) cells = capacity_add(cells, module->cells_size());
						budget.finish(abc, cells, script_kind, sequential);
					} else budget.reserved_work = 0;
					post.cancel(candidate);
					clear_pending();
					double elapsed = Lut4Mapping::PostTiming::seconds(FsmLimits::Clock::now() - start);
					incomplete_mapping_seconds += elapsed;
					log("opt_fsm_lut4: incomplete candidate construction=%s status=LimitReached reason=%s actual seconds=%.9f cumulative incomplete mapping seconds=%.9f ABC executions=%d.\n",
						construction, budget.limit_reason, elapsed, incomplete_mapping_seconds, abc.executions);
					return Lut4Mapping::AuditResult{};
				}
				abc = audit.finish();
			}
			saved.check_empty();
			log_debug("opt_fsm_lut4: ABC clone/helper reservation=%lld clone=%lld helpers=%lld actual saved helper peak=%lld actual auxiliary helper peak=%lld map peak=%lld unmap peak=%lld holes peak=%lld external estimate=%lld bytes.\n",
				(long long)capacity_add(abc_prepaid_clone, abc_prepaid_helpers), (long long)abc_prepaid_clone, (long long)abc_prepaid_helpers,
				(long long)abc_saved_peak, (long long)abc_helper_peak, (long long)helper_peak[0], (long long)helper_peak[1],
				(long long)helper_peak[2], (long long)abc_external);
			Pass::call(candidate, "check -assert");
			int64_t mapped_cells = 0;
			for (auto module : candidate->selected_modules()) mapped_cells += module->cells_size();
			budget.finish(abc, mapped_cells, script_kind, sequential);
			candidate_cost = metrics(candidate);
			post.finish(candidate, candidate_cost.first, candidate_cost.second);
			candidate->scratchpad_unset("opt_fsm_lut4.evaluating");
			candidate->scratchpad_unset("opt_lut4_mapping.evaluating");
			candidate->scratchpad_unset("opt_lut4_mapping.carry_mode");
			auto finished = FsmLimits::Clock::now();
			log_assert(post.timing.measured && start <= post.timing.started && post.timing.finished <= finished);
			last_cell_tail_duration = finished - post.timing.finished;
			if (abc_finished != FsmLimits::Clock::time_point()) {
				log_assert(abc_finished <= post.timing.started);
				last_post_setup_duration = post.timing.started - abc_finished;
			}
			log_debug("opt_fsm_lut4: suffix stage runtime construction=%s ABC=%.9f post setup=%.9f physical tail=%.9f seconds.\n", construction,
				Lut4Mapping::PostTiming::seconds(last_abc_duration), Lut4Mapping::PostTiming::seconds(last_post_setup_duration),
				Lut4Mapping::PostTiming::seconds(last_cell_tail_duration));
			last_mapping_duration = finished - start;
			log_assert(post.timing.complete <= last_mapping_duration);
			double elapsed = Lut4Mapping::PostTiming::seconds(last_mapping_duration);
			double core_seconds = Lut4Mapping::PostTiming::seconds(last_mapping_duration - post.timing.complete);
			double measured_prefix = Lut4Mapping::PostTiming::seconds(last_prefix_duration);
			double capture_seconds = Lut4Mapping::PostTiming::seconds(last_capture_duration);
			double clone_seconds = Lut4Mapping::PostTiming::seconds(reuse_duration);
			log_assert(measured_prefix + capture_seconds + clone_seconds <= core_seconds);
			double suffix_seconds = core_seconds - measured_prefix - capture_seconds - clone_seconds;
			complete_mapping_seconds += elapsed;
			core_estimates[int(script_kind)] = suffix_seconds + (prefix_context.measured ? measured_prefix : prefix_seconds);
			suffix_estimates[int(script_kind)] = suffix_seconds;
			log_debug("opt_fsm_lut4: prefix/suffix runtime construction=%s script=%s prefix seconds=%.9f capture seconds=%.9f clone/transfer seconds=%.9f suffix core seconds=%.9f cache=%s.\n",
				construction, Lut4Mapping::script_name(script_kind), measured_prefix, capture_seconds, clone_seconds, suffix_seconds, reuse ? "hit" : "miss");
			log_debug("opt_fsm_lut4: mapping runtime construction=%s script=%s carry_mode=%s complete seconds=%.9f cumulative mapping seconds=%.9f core seconds=%.9f shared post seconds=%.9f lookup seconds=%.9f resyn seconds=%.9f resub seconds=%.9f cleanup seconds=%.9f.\n",
				construction, sequential ? "sequential" : Lut4Mapping::script_name(script_kind), native ? "native" : "generic", elapsed, complete_mapping_seconds,
				core_seconds, Lut4Mapping::PostTiming::seconds(post.timing.complete), Lut4Mapping::PostTiming::seconds(post.timing.lookup),
				Lut4Mapping::PostTiming::seconds(post.timing.resyn), Lut4Mapping::PostTiming::seconds(post.timing.resub),
				Lut4Mapping::PostTiming::seconds(post.timing.cleanup()));
			log_debug("opt_fsm_lut4: late carry runtime setup=%.9f search=%.9f complete=%.9f seconds work=%lld.\n",
				Lut4Mapping::PostTiming::seconds(post.timing.carry_setup()), Lut4Mapping::PostTiming::seconds(post.timing.carry_search),
				Lut4Mapping::PostTiming::seconds(post.timing.carry), (long long)post.timing.carry_work);
			last_mapping_success = true; return abc;
		};
		// 必要 baseline 在所有推测分析及名字生成之前完成，全部实际消费均记录。
		budget.work = 0;
		budget.actual_work += 1024 + source_cells * 64;
		log("opt_fsm_lut4: required baseline construction proxy=%lld; mapping allowance is calibrated after the complete generic baseline.\n",
			(long long)(1024 + source_cells * 64));
		budget.begin(1024 + source_cells * 64, true);
		auto best = clone_design(design);
		Lut4Mapping::AuditResult baseline_abc;
		{
			FsmPrefixKey key {design, nullptr, "cycloneiv" + options, "normal", {}, {}};
			baseline_abc = map(best.get(), Lut4Mapping::ScriptKind::AreaLutpack, "normal", false, key, false, design_storage,
				sequential ? capacity_add(capacity_mul(source_cells, 32), capacity_mul(source_wires, 16)) :
				Lut4Mapping::mapping_workspace(Lut4Mapping::ScriptKind::AreaLutpack, source_cells, source_wires), true);
			log_assert(last_mapping_success);
		}
		int64_t rss = process_peak_bytes();
		auto baseline = candidate_cost, best_cost = baseline;
		complete_generic(baseline, baseline.second);
		post.select(best.get());
		int64_t baseline_capacity = design_capacity(best.get());
		design_storage.resize_required(capacity_add(source_capacity, baseline_capacity));
		int64_t source_mux_index = mux_index_capacity(design);
		int64_t post_index = post_capacity(best.get(), true);
		int64_t resub_index = post_capacity(best.get(), false);
		int64_t carry_index = sequential ? 0 : carry_capacity(best.get());
		int64_t carry_workspace = sequential ? 0 : carry_workspace_limit(best.get(), carry_index);
		int64_t abc_workspace = Lut4Mapping::mapping_workspace(Lut4Mapping::ScriptKind::CascadeArea, baseline_abc.nodes, baseline_abc.wires);
		int64_t helper_workspace = 0;
		for (auto bytes : baseline_helper_capacity) helper_workspace = capacity_add(helper_workspace, bytes);
		int64_t workspaces = std::max({capacity_add(source_mux_index, 16 * 1048576),
			capacity_add(post_index, Lut4Mapping::post_resyn_workspace), capacity_add(resub_index, Lut4Mapping::post_resub_workspace),
			capacity_add(carry_index, carry_workspace),
			capacity_add(abc_workspace, helper_workspace)});
		int64_t resident = budget.bytes - prefix_storage.bytes;
		log_assert(resident >= 0);
		int64_t growth = std::min<int64_t>(16 * 1048576, std::max<int64_t>(1048576, capacity_add(source_capacity, baseline_capacity) / 8));
		int64_t calibration_capacity = std::max({source_capacity, baseline_capacity, baseline_phase_capacity});
		int64_t extra = std::min(capacity_mul(2, rss), std::max<int64_t>(64 * 1048576,
			capacity_add(capacity_mul(2, calibration_capacity), capacity_add(workspaces, growth))));
		int64_t automatic_memory = std::min<int64_t>(1024 * 1048576, std::max<int64_t>(64 * 1048576, capacity_add(resident, extra)));
		budget.memory = explicit_memory ? explicit_memory : automatic_memory;
		log("opt_fsm_lut4: frozen memory calibration S=%lld B=%lld phase_C=%lld phase_modules=%lld C=%lld L=%lld J=%lld P=%lld P_resub=%lld A=%lld H=%lld W=%lld G=%lld R=%lld E=%lld auto=%lld explicit=%lld memory=%lld prefix=%lld bytes.\n",
			(long long)source_capacity, (long long)baseline_capacity, (long long)baseline_phase_capacity, (long long)baseline_module_capacity, (long long)calibration_capacity,
			(long long)resident, (long long)source_mux_index, (long long)post_index, (long long)resub_index,
			(long long)abc_workspace, (long long)helper_workspace, (long long)workspaces, (long long)growth, (long long)rss, (long long)extra,
			(long long)automatic_memory, (long long)explicit_memory, (long long)budget.memory, (long long)prefix_storage.bytes);
		log("opt_fsm_lut4: frozen carry memory calibration index=%lld workspace=%lld bytes.\n",
			(long long)carry_index, (long long)carry_workspace);
		int64_t source_ast = design_ast_capacity(design), baseline_ast = design_ast_capacity(best.get());
		log("opt_fsm_lut4: Design structural capacity source AST=%lld remaining=%lld baseline AST=%lld remaining=%lld; independent AST ownership retained.\n",
			(long long)source_ast, (long long)(source_capacity - source_ast), (long long)baseline_ast, (long long)(baseline_capacity - baseline_ast));
		int64_t baseline_effort = 0;
		for (auto module : best->selected_modules()) baseline_effort += int64_t(module->cells_size()) * 64;
		baseline_effort += baseline_abc.nodes * 256 + baseline_abc.wires * 32;
		log_assert(baseline_effort >= 0 && baseline_effort <= INT64_MAX / 16);
		int64_t calibrated_limit = std::min(mapping_work_limit, baseline_effort * 16);
		budget.work = std::max<int64_t>(0, calibrated_limit - budget.actual_work);
		auto baseline_post = post.timing;
		auto baseline_core_duration = last_mapping_duration - baseline_post.complete;
		double baseline_seconds = Lut4Mapping::PostTiming::seconds(last_mapping_duration);
		double baseline_core_seconds = Lut4Mapping::PostTiming::seconds(baseline_core_duration);
		auto baseline_suffix_duration = baseline_core_duration - last_prefix_duration - last_capture_duration;
		log_assert(baseline_suffix_duration >= FsmLimits::Clock::duration::zero());
		auto common_mux_duration = Lut4Mapping::CommonMuxContext::measured_duration(design);
		auto additional_duration = std::max(FsmLimits::Clock::duration::zero(), 8 * baseline_suffix_duration - common_mux_duration);
		auto deadline_duration = last_mapping_duration + additional_duration;
		double deadline_seconds = Lut4Mapping::PostTiming::seconds(deadline_duration);
		budget.deadline = budget.started + deadline_duration;
		log("opt_fsm_lut4: deadline calibration full ticks=%lld suffix core ticks=%lld common Mux ticks=%lld additional ticks=%lld deadline ticks=%lld optional factor=8.\n",
			(long long)last_mapping_duration.count(), (long long)baseline_suffix_duration.count(), (long long)common_mux_duration.count(),
			(long long)additional_duration.count(), (long long)deadline_duration.count());
		double baseline_suffix_seconds = Lut4Mapping::PostTiming::seconds(baseline_suffix_duration);
		double baseline_prefix_seconds = Lut4Mapping::PostTiming::seconds(last_prefix_duration);
		core_estimates[int(Lut4Mapping::ScriptKind::CascadeArea)] = baseline_prefix_seconds + 1.5 * baseline_suffix_seconds;
		core_estimates[int(Lut4Mapping::ScriptKind::RewriteRefactor)] = baseline_prefix_seconds + 1.25 * baseline_suffix_seconds;
		core_estimates[int(Lut4Mapping::ScriptKind::ExpandedCuts)] = baseline_prefix_seconds + 2 * baseline_suffix_seconds;
		suffix_estimates[int(Lut4Mapping::ScriptKind::CascadeArea)] = 1.5 * baseline_suffix_seconds;
		suffix_estimates[int(Lut4Mapping::ScriptKind::RewriteRefactor)] = 1.25 * baseline_suffix_seconds;
		suffix_estimates[int(Lut4Mapping::ScriptKind::ExpandedCuts)] = 2 * baseline_suffix_seconds;
		if (feedback_enabled) {
			double baseline_feedback_core = Lut4Mapping::PostTiming::seconds(2 * last_abc_duration + last_cell_tail_duration + last_post_setup_duration);
			core_estimates[int(Lut4Mapping::ScriptKind::FeedbackBoolean)] = baseline_feedback_core;
			suffix_estimates[int(Lut4Mapping::ScriptKind::FeedbackBoolean)] = baseline_feedback_core;
		}
		log("opt_fsm_lut4: generic baseline LUT4=%lld DFF=%lld raw proxy=%lld mapping limit=%lld charged=%lld remaining=%lld, full tail=%.9f seconds core tail=%.9f seconds shared post=%.9f seconds suffix core=%.9f seconds common Mux=%.9f seconds additional suffix allowance=%.9f seconds deadline=%.9f seconds from coordinator start, optional time remaining=%.9f seconds.\n",
			(long long)baseline.first, (long long)baseline.second, (long long)baseline_effort, (long long)calibrated_limit,
			(long long)budget.actual_work, (long long)budget.work, baseline_seconds, baseline_core_seconds,
			Lut4Mapping::PostTiming::seconds(baseline_post.complete), baseline_suffix_seconds, Lut4Mapping::PostTiming::seconds(common_mux_duration),
			Lut4Mapping::PostTiming::seconds(additional_duration), deadline_seconds,
			std::max(0.0, std::chrono::duration<double>(budget.deadline - FsmLimits::Clock::now()).count()));
		log("opt_fsm_lut4: post prediction uses measured lookup/cleanup and carry setup plus resyn/resub/carry search seconds times their published local allowance; carry reservation is included once in the resub global pool.\n");
		auto complete = [&]() {
			evict_prefix("coordinator completed");
			clear_pending(); best_eligible_generic.reset(); generic_storage.resize_required(0);
			for (auto module : design->selected_modules()) {
				auto replacement = best->module(module->name); log_assert(replacement);
				for (auto wire : module->wires()) if (wire->port_id) {
					auto port = replacement->wire(wire->name);
					log_assert(port && port->width == wire->width && port->port_id == wire->port_id && port->start_offset == wire->start_offset && port->upto == wire->upto && port->is_signed == wire->is_signed && port->port_input == wire->port_input && port->port_output == wire->port_output);
				}
			}
			int64_t completed_capacity = design_capacity(best.get());
			design_storage.resize_required(std::max(capacity_add(source_capacity, completed_capacity), capacity_mul(2, completed_capacity)));
			log("opt_fsm_lut4: required transfer resident=%lld memory=%lld required_overage=%lld bytes.\n", (long long)budget.bytes,
				(long long)budget.memory, (long long)std::max<int64_t>(0, budget.bytes - budget.memory));
			Lut4Mapping::transfer(design, best.get());
			design->scratchpad_set_bool("opt_fsm_lut4.completed", true);
			log("opt_fsm_lut4: completed %d full mappings, accepted LUT4=%lld DFF=%lld, workspace peak=%lld bytes, clone cells=%lld, ABC executions=%d, AIG nodes=%lld, AIG wires=%lld, construction and ABC mapping proxy work=%lld, reservation peak=%lld.\n",
				budget.completed_mappings, (long long)best_cost.first, (long long)best_cost.second, (long long)budget.peak_bytes,
				(long long)source_cells, budget.abc_executions, (long long)budget.aig_nodes, (long long)budget.aig_wires, (long long)budget.actual_work, (long long)budget.peak_reserved_work);
			log("opt_fsm_lut4: postprocessing resyn work=%lld, resub work=%lld, SAT effort=%lld, post workspace peak=%lld, structure cache=%lld bytes.\n",
				(long long)post.budget.resyn_work, (long long)post.budget.resub_work, (long long)post.budget.sat_work, (long long)post.budget.peak, (long long)post.bytes());
			log("opt_fsm_lut4: postprocessing carry work=%lld truth=%lld/%lld resub global remaining=%lld/%lld.\n",
				(long long)post.budget.carry_work, (long long)post.budget.truth_work, (long long)post.budget.truth_limit,
				(long long)post.budget.resub, (long long)post.budget.resub_limit);
			log("opt_fsm_lut4: reservation limit=%lld bytes, skipped work=%d memory=%d cascade work=%d, complete mapping seconds=%.6f, raw mapping proxy=%lld.\n",
				(long long)budget.memory, skipped.work, skipped.memory, skipped.cascade_work, complete_mapping_seconds, (long long)budget.raw_mapping_work);
			log("opt_fsm_lut4: actual mapping seconds=%.9f complete=%.9f incomplete=%.9f common Mux actual seconds=%.9f.\n",
				complete_mapping_seconds + incomplete_mapping_seconds, complete_mapping_seconds, incomplete_mapping_seconds,
				Lut4Mapping::PostTiming::seconds(common_mux_duration));
			log("opt_fsm_lut4: feedback enabled=%d captures=%d checkpoint reservation peak=%lld capture proxy=%lld capture seconds=%.9f attempt proxy=%lld attempt seconds=%.9f full mappings=%d ABC executions=%d resyn work=%lld resub work=%lld SAT effort=%lld.\n",
				feedback_enabled ? 1 : 0, feedback_stats.captures, (long long)feedback_stats.checkpoint_peak, (long long)feedback_stats.capture_work,
				feedback_stats.capture_seconds, (long long)feedback_stats.work, feedback_stats.seconds, feedback_stats.mappings, feedback_stats.abc_executions,
				(long long)feedback_stats.resyn_work, (long long)feedback_stats.resub_work, (long long)feedback_stats.sat_work);
			log("opt_fsm_lut4: FSM analysis work=%lld remaining=%lld SAT remaining=%lld; deadline skips=%d actual coordinator seconds=%.6f deadline seconds=%.6f mapping limit=%lld remaining=%lld.\n",
				(long long)budget.analysis_actual, (long long)budget.analysis_work, (long long)budget.sat, skipped.deadline,
				std::chrono::duration<double>(FsmLimits::Clock::now() - budget.started).count(), deadline_seconds,
				(long long)calibrated_limit, (long long)budget.work);
		};
		auto run_feedback = [&]() {
			if (sequential || !best_eligible_generic || budget.completed_mappings >= budget.mappings) {
				log("opt_fsm_lut4: feedback generation=1 skipped reason=%s.\n", sequential ? "sequential configuration" : !best_eligible_generic ? "no eligible generic checkpoint" : "complete mapping allowance");
				return;
			}
			double post_prediction = baseline_post.predict(post.budget);
			double preparation_prediction = std::max(20 * prefix_clone_seconds, baseline_suffix_seconds / 10);
			double prediction = preparation_prediction + suffix_estimates[int(Lut4Mapping::ScriptKind::FeedbackBoolean)] + post_prediction;
			log("opt_fsm_lut4: feedback generation=1 prediction preparation=%.9f suffix=%.9f post=%.9f total=%.9f elapsed=%.9f deadline=%.9f seconds shared resyn remaining=%lld/%lld resub remaining=%lld/%lld SAT remaining=%lld/4000000.\n",
				preparation_prediction, suffix_estimates[int(Lut4Mapping::ScriptKind::FeedbackBoolean)], post_prediction, prediction,
				std::chrono::duration<double>(FsmLimits::Clock::now() - budget.started).count(), deadline_seconds,
				(long long)post.budget.resyn, (long long)post.budget.resyn_limit, (long long)post.budget.resub, (long long)post.budget.resub_limit, (long long)post.budget.sat);
			if (!budget.time_available(prediction)) { skipped.deadline++; log("opt_fsm_lut4: feedback generation=1 status=LimitReached reason=complete preparation and tail deadline.\n"); return; }
			evict_prefix("feedback seed consumption");
			auto seed = std::move(best_eligible_generic);
			auto candidate = std::move(seed->design);
			seed->source_key = {};
			generic_storage.resize_required(0);
			FsmStorage candidate_storage(budget), seed_storage(budget), preparation_storage(budget);
			candidate_storage.resize_required(design_capacity(candidate.get()));
			seed_storage.resize_required(seed->metadata_capacity());
			Lut4Mapping::FeedbackResources resources;
			resources.available = [&]() { return budget.time_available() && budget.bytes <= budget.memory; };
			resources.spend = [&](int64_t amount) { return budget.spend_mapping(amount); };
			resources.reserve = [&](int64_t growth, int64_t indexes) {
				return candidate_storage.resize(capacity_add(design_capacity(candidate.get()), growth)) &&
					preparation_storage.resize(capacity_add(indexes, 4 * 1048576));
			};
			resources.observe = [&]() { candidate_storage.resize_required(design_capacity(candidate.get())); };
			auto preparation_started = FsmLimits::Clock::now();
			auto prepared = Lut4Mapping::prepare_feedback(candidate.get(), resources);
			double preparation_seconds = std::chrono::duration<double>(FsmLimits::Clock::now() - preparation_started).count();
			preparation_storage.resize_required(0);
			log_debug("opt_fsm_lut4: feedback generation=1 source construction=%s source script=%s source LUT4=%lld DFF=%lld preparation status=%s reason=%s seconds=%.9f proxy=%lld expansion E=%lld.\n",
				seed->identity.construction, Lut4Mapping::script_name(seed->script_kind), (long long)seed->cost.first, (long long)seed->cost.second,
				prepared.status == Lut4Mapping::FeedbackStatus::Prepared ? "Prepared" : prepared.status == Lut4Mapping::FeedbackStatus::Unsupported ? "Unsupported" : "LimitReached",
				prepared.reason, preparation_seconds, (long long)prepared.work, (long long)prepared.expansion);
			if (prepared.status != Lut4Mapping::FeedbackStatus::Prepared) return;
			int64_t cells = 0, bits = 0, aig_nodes = 0, aig_wires = 0;
			int64_t estimator_work = Lut4Mapping::feedback_scan_work(candidate.get());
			FsmStorage estimator_storage(budget);
			if (!budget.time_available() || !estimator_storage.reserve(65536) || !budget.spend_mapping(estimator_work)) return;
			auto estimator_started = FsmLimits::Clock::now();
			for (auto module : candidate->selected_modules()) {
				cells = capacity_add(cells, module->cells_size());
				for (auto wire : module->wires()) bits = capacity_add(bits, wire->width);
				for (auto cell : module->cells()) if (!Lut4Mapping::boundary(cell, candidate.get())) {
					Aig aig(cell);
					if (aig.name.empty()) log_error("opt_fsm_lut4: unsupported feedback AIG cell %s.%s.\n", module, cell);
					for (auto &node : aig.nodes) if (node.left_parent >= 0 && node.right_parent >= 0) aig_nodes++;
					aig_wires = capacity_add(aig_wires, aig.nodes.size());
				}
			}
			if (!aig_wires) {
				log("opt_fsm_lut4: feedback generation=1 status=Unsupported reason=no nonempty combinational ABC network after preparation.\n");
				return;
			}
			int64_t estimate = Lut4Mapping::mapping_effort(Lut4Mapping::ScriptKind::FeedbackBoolean,
				std::max(baseline_effort, capacity_add(capacity_mul(cells, 64), capacity_add(capacity_mul(aig_nodes, 256), capacity_mul(aig_wires, 32)))));
			int64_t workspace = Lut4Mapping::mapping_workspace(Lut4Mapping::ScriptKind::FeedbackBoolean,
				std::max(aig_nodes, baseline_abc.nodes), std::max(aig_wires, baseline_abc.wires));
			log_debug("opt_fsm_lut4: feedback generation=1 actual preparation AIG estimate nodes=%lld wires=%lld cells=%lld signal bits=%lld ABC workspace=%lld estimator proxy=%lld seconds=%.9f.\n",
				(long long)aig_nodes, (long long)aig_wires, (long long)cells, (long long)bits, (long long)workspace, (long long)estimator_work,
				std::chrono::duration<double>(FsmLimits::Clock::now() - estimator_started).count());
			estimator_storage.resize_required(0);
			int64_t helpers = 0;
			for (auto value : abc_helper_capacity(candidate.get(), false)) helpers = capacity_add(helpers, value);
			int64_t abc_reservation = capacity_add(abc_clone_capacity(candidate.get()), capacity_add(helpers, workspace));
			FsmStorage admission(budget);
			if (!budget.time_available(prediction - preparation_prediction) || !budget.begin(estimate) || !admission.reserve(abc_reservation)) {
				budget.reserved_work = 0;
				log("opt_fsm_lut4: feedback generation=1 status=LimitReached reason=complete ABC tail resource allowance work=%lld workspace=%lld remaining=%lld memory=%lld.\n",
					(long long)estimate, (long long)abc_reservation, (long long)budget.work, (long long)(budget.memory - budget.bytes));
				return;
			}
			admission.resize_required(0);
			auto feedback_abc = map(candidate.get(), Lut4Mapping::ScriptKind::FeedbackBoolean, "feedback-generation-1", seed->native,
				seed->identity, false, candidate_storage, workspace, false, {}, true);
			if (!last_mapping_success) return;
			if (!feedback_abc.executions) log_error("opt_fsm_lut4: prepared nonempty feedback network had no real ABC execution.\n");
			auto cost = candidate_cost;
			log("opt_fsm_lut4: feedback generation=1 complete LUT4=%lld DFF=%lld current best LUT4=%lld baseline DFF=%lld source LUT4=%lld.\n",
				(long long)cost.first, (long long)cost.second, (long long)best_cost.first, (long long)baseline.second, (long long)seed->cost.first);
			if (cost.first < best_cost.first && cost.second <= baseline.second) {
				best = std::move(candidate); best_cost = cost; post.select(best.get());
				best_task = {seed->identity.construction, seed->identity.codes, Lut4Mapping::ScriptKind::FeedbackBoolean, false, seed->native,
					TaskKind::Feedback, seed->script_kind};
				best_emissions = std::move(seed->identity.emissions);
				int64_t emission_bytes = capacity_mul(best_emissions.capacity(), sizeof(FsmEmissionPlan));
				for (auto &emission : best_emissions) emission_bytes = capacity_add(emission_bytes, emission.capacity());
				best_emission_storage.resize_required(emission_bytes);
				candidate_storage.resize_required(0); design_storage.resize_required(capacity_add(source_capacity, design_capacity(best.get())));
			}
		};
		auto feedback = [&]() {
			if (!feedback_enabled || feedback_attempted) return;
			feedback_attempted = true;
			auto started = FsmLimits::Clock::now();
			int64_t work = budget.actual_work, resyn = post.budget.resyn_work, resub = post.budget.resub_work, sat = post.budget.sat_work;
			int mappings = budget.completed_mappings, executions = budget.abc_executions;
			run_feedback();
			feedback_stats.work = budget.actual_work - work;
			feedback_stats.seconds = Lut4Mapping::PostTiming::seconds(FsmLimits::Clock::now() - started);
			feedback_stats.mappings = budget.completed_mappings - mappings;
			feedback_stats.abc_executions = budget.abc_executions - executions;
			feedback_stats.resyn_work = post.budget.resyn_work - resyn;
			feedback_stats.resub_work = post.budget.resub_work - resub;
			feedback_stats.sat_work = post.budget.sat_work - sat;
		};
		if (budget.completed_mappings >= budget.mappings) { complete(); return; }
		std::vector<FsmModel> models; std::vector<std::vector<FsmPlan>> plans;
		FsmStorage model_storage(budget);
		auto analyze = [&]() {
		FsmStorage analysis_storage(budget);
		if (!budget.spend(1024 + source_cells * 16) || !analysis_storage.reserve(source_capacity) || !budget.spend_mapping(1024 + source_cells * 64)) return;
		auto analysis = clone_design(design);
		if (!expand_state_roms(analysis.get(), budget)) return;
		if (!budget.time_available()) return;
		Pass::call(analysis.get(), "fsm -nomap -norecode");
		analysis_storage.resize_required(design_capacity(analysis.get()));
		if (budget.bytes > budget.memory) return;
		dict<IdString, pool<IdString>> owned; int64_t model_nodes = 0;
		for (auto module : analysis->selected_modules()) {
			if (!budget.time_available()) return;
			FsmStorage index_storage(budget);
			if (!budget.spend(64 + int64_t(module->cells_size()) * 16) || !index_storage.reserve(int64_t(module->cells_size()) * 512)) continue;
			FsmIndex index(module);
			for (auto cell : module->cells()) {
				if (!budget.time_available() || budget.analysis_work == 0) return;
				FsmModel model;
				if (cell->type == ID($fsm) && !cell->get_bool_attribute(ID::keep)) {
					auto encoding = cell->attributes.find(ID::fsm_encoding);
					if (encoding != cell->attributes.end() && (encoding->second.decode_string() == "none" || encoding->second.decode_string() == "user")) continue;
					model.module = module->name; model.cell = cell->name; model.data.copy_from_cell(cell);
					model.fsm_name = cell->getParam(ID::NAME).decode_string();
					model.inputs = cell->getPort(ID::CTRL_IN); model.outputs = cell->getPort(ID::CTRL_OUT);
					if (GetSize(model.data.state_table) < 2 || GetSize(model.data.state_table) > budget.states || GetSize(model.data.transition_table) > budget.transitions || model.data.num_inputs > 128 || model.data.num_outputs > 256) continue;
				} else if (StaticCellTypes::categories.is_ff(cell->type)) {
					FsmExtractor extractor(index, budget); if (!extractor.run(cell)) continue; model = std::move(extractor.model);
				} else continue;
				model.width_limit = model.data.state_bits;
				if (!model.extracted) {
					int states = GetSize(model.data.state_table), binary_width = 1; while ((1 << binary_width) < states) binary_width++;
					model.width_limit = states < 32 ? states : binary_width;
					if (cell->attributes.count(ID::fsm_encoding) && cell->attributes.at(ID::fsm_encoding).decode_string() == "binary") model.width_limit = binary_width;
				}
				bool overlap = owned[module->name].count(model.cell);
				for (auto name : model.removed) if (owned[module->name].count(name)) overlap = true;
				if (overlap) continue;
				model_nodes += GetSize(model.data.state_table) + GetSize(model.data.transition_table);
				if (model_nodes > budget.nodes) continue;
				auto candidates = plans_for(model, budget); if (candidates.empty()) continue;
				if (!model_storage.reserve(int64_t(GetSize(model.data.transition_table)) * (256 + 4 * (model.data.num_inputs + model.data.num_outputs)) + int64_t(GetSize(candidates)) * GetSize(model.data.state_table) * (128 + model.width_limit))) continue;
				model.saved_inputs = save_signal(model.inputs); model.saved_outputs = save_signal(model.outputs);
				model.inputs = SigSpec(); model.outputs = SigSpec(); model.q = SigSpec(); model.d = SigSpec();
				owned[module->name].insert(model.cell); for (auto name : model.removed) owned[module->name].insert(name);
				models.push_back(std::move(model)); plans.push_back(std::move(candidates));
			}
		}
		};
		if (source_cells <= 100000) analyze();
		bool arithmetic_opportunity = false;
		for (auto module : design->selected_unboxed_modules()) for (auto cell : module->cells())
			if (!cell->has_keep_attr() && cell->type.in(ID($alu), ID($fa), ID($add), ID($sub), ID($mul), ID($macc), ID($macc_v2)))
				arithmetic_opportunity = true;
		std::vector<Task> tasks;
		FsmStorage pool_storage(budget);
		// 任务对象、共享编码及全部 mapping 身份在创建容器之前取得容量。
		int64_t pool_estimate = capacity_add(capacity_mul(80, sizeof(Task) + 128), capacity_mul(budget.mappings, 1024));
		for (auto &model : models) pool_estimate = capacity_add(pool_estimate,
			capacity_add(128, capacity_mul(model.data.state_table.size(), capacity_add(1024, capacity_mul(model.width_limit, 16)))));
		for (auto &choices : plans) for (auto &plan : choices) pool_estimate = capacity_add(pool_estimate,
			capacity_mul(plan.codes.capacity(), capacity_add(sizeof(Const), budget.states)));
		if (!pool_storage.reserve(pool_estimate)) { if (feedback_enabled) feedback(); complete(); return; }
		tasks.reserve(80);
		std::vector<std::vector<Const>> original;
		for (auto &model : models) original.push_back(model.data.state_table);
		auto original_codes = std::make_shared<const std::vector<std::vector<Const>>>(std::move(original));
		if (!models.empty()) tasks.push_back({"original-encoding", original_codes, Lut4Mapping::ScriptKind::AreaLutpack});
		std::vector<Task> ranked;
		for (int rank = 0; !models.empty() && rank < 2; rank++) {
			auto candidate = *original_codes;
			for (int i = 0; i < GetSize(models); i++) {
				auto ordered = plans[i]; std::stable_sort(ordered.begin(), ordered.end(), [](const FsmPlan &a, const FsmPlan &b) { return a.cost < b.cost; });
				candidate[i] = ordered[std::min(rank, GetSize(ordered) - 1)].codes;
			}
			ranked.push_back({stringf("encoding-rank-%d", rank + 1), std::make_shared<const std::vector<std::vector<Const>>>(std::move(candidate)), rank == 0 ? Lut4Mapping::ScriptKind::CascadeArea : Lut4Mapping::ScriptKind::RewriteRefactor});
		}
		if (!ranked.empty()) tasks.push_back(ranked.front());
		if (models.empty() && !sequential) {
			tasks.push_back({"normal", {}, Lut4Mapping::ScriptKind::CascadeArea});
		}
		if (arithmetic_opportunity && !sequential)
			tasks.push_back({"current-best", {}, Lut4Mapping::ScriptKind::AreaLutpack, true, true});
		if (ranked.size() > 1) tasks.push_back(ranked[1]);
		if (models.empty() && !sequential) tasks.push_back({"normal", {}, Lut4Mapping::ScriptKind::RewriteRefactor});
		// 全部构造与脚本进入候选池，预定机会未执行时继续使用剩余额度。
		std::vector<Task> constructions {{"normal", {}, Lut4Mapping::ScriptKind::AreaLutpack}};
		if (!models.empty()) constructions.push_back({"original-encoding", original_codes, Lut4Mapping::ScriptKind::AreaLutpack});
		constructions.insert(constructions.end(), ranked.begin(), ranked.end());
		for (auto &construction : constructions) if (!sequential)
			for (auto kind : {Lut4Mapping::ScriptKind::AreaLutpack, Lut4Mapping::ScriptKind::CascadeArea, Lut4Mapping::ScriptKind::RewriteRefactor, Lut4Mapping::ScriptKind::ExpandedCuts}) {
				for (bool use_carry : {false, true}) {
					if (use_carry && !arithmetic_opportunity) continue;
					auto task = construction; task.script_kind = kind; task.native = use_carry;
					tasks.push_back(std::move(task));
				}
			}
		struct Identity { Task task; std::vector<FsmEmissionPlan> emissions; };
		std::vector<Identity> attempted {{best_task, {}}};
		attempted.reserve(budget.mappings);
		log_debug("opt_fsm_lut4: construction identity capacity=%lld mapping allowance=%d reservation=%lld bytes.\n",
			(long long)attempted.capacity(), budget.mappings, (long long)capacity_mul(attempted.capacity(), sizeof(Identity)));
		auto same_task = [&](const Task &left, const Task &right) {
			return left.construction == right.construction && ((!left.codes && !right.codes) || (left.codes && right.codes && *left.codes == *right.codes)) &&
				(sequential || left.script_kind == right.script_kind) && left.native == right.native && left.kind == right.kind;
		};
		auto task_bytes = [](const Task &task) {
			return int64_t(task.construction.capacity());
		};
		auto account_pool = [&]() {
			int64_t bytes = capacity_add(sizeof(Task), capacity_add(capacity_mul(capacity_add(tasks.capacity(), capacity_add(constructions.capacity(), ranked.capacity())), sizeof(Task)),
				capacity_mul(attempted.capacity(), sizeof(Identity))));
			std::set<const std::vector<std::vector<Const>> *> shared_codes;
			shared_codes.insert(original_codes.get());
			auto record = [&](const Task &task) { bytes = capacity_add(bytes, task_bytes(task)); if (task.codes) shared_codes.insert(task.codes.get()); };
			for (auto &task : tasks) record(task);
			for (auto &task : constructions) record(task);
			for (auto &task : ranked) record(task);
			record(best_task);
			for (auto &identity : attempted) {
				record(identity.task); bytes = capacity_add(bytes, capacity_mul(identity.emissions.capacity(), sizeof(FsmEmissionPlan)));
				for (auto &emission : identity.emissions) bytes = capacity_add(bytes, emission.capacity());
			}
			for (auto codes : shared_codes)
				bytes = capacity_add(bytes, codes_capacity(*codes, int64_t(64 + sizeof(*codes))));
			pool_storage.resize_required(bytes);
		};
		account_pool();
		size_t task_index = 0;
		while (budget.completed_mappings < budget.mappings && (task_index < tasks.size() || (feedback_enabled && !feedback_attempted))) {
			if (feedback_enabled && !feedback_attempted && (optional_completed || task_index >= tasks.size())) { feedback(); account_pool(); }
			if (budget.completed_mappings >= budget.mappings || task_index >= tasks.size()) break;
			auto task = tasks[task_index++];
			if (task.use_best) {
				task.construction = best_task.construction; task.codes = best_task.codes;
				task.script_kind = best_task.kind == TaskKind::Feedback ? best_task.source_script : best_task.script_kind;
			}
			bool generic_script_variation = !task.codes && task.construction == "normal" && !task.native &&
				task.kind == TaskKind::Ordinary && task.script_kind != Lut4Mapping::ScriptKind::AreaLutpack;
			if (feedback_enabled && !feedback_attempted && generic_script_variation) {
				log("opt_fsm_lut4: generic checkpoint feedback precedes script-only variation script=%s.\n", Lut4Mapping::script_name(task.script_kind));
				feedback(); account_pool();
				if (budget.completed_mappings >= budget.mappings) break;
			}
			bool duplicate = false;
			for (auto &previous : attempted)
				if (!task.codes && same_task(previous.task, task)) duplicate = true;
			if (duplicate) continue;
			int64_t construction_work = 1024 + source_cells * 64;
			int64_t estimate = (sequential ? baseline_effort : Lut4Mapping::mapping_effort(task.script_kind, baseline_effort)) + construction_work;
			FsmStorage key_storage(budget);
			if (!key_storage.reserve(capacity_add(sizeof(FsmPrefixKey), capacity_add(capacity_mul(options.capacity(), 2), capacity_add(capacity_mul(task.construction.capacity(), 2), 1024))))) {
				skipped.memory++; continue;
			}
			FsmPrefixKey candidate_key {design, task.codes ? &models : nullptr, "cycloneiv" + options, task.construction, task.codes, {}};
			key_storage.resize_required(candidate_key.capacity());
			if (budget.bytes > budget.memory) evict_prefix("candidate key admission");
			auto same_prefix_construction = [&]() {
				if (!prefix_cache) return false;
				return prefix_key.source == candidate_key.source && prefix_key.models == candidate_key.models &&
					prefix_key.configuration == candidate_key.configuration && prefix_key.construction == candidate_key.construction &&
					((!prefix_key.codes && !candidate_key.codes) || (prefix_key.codes && candidate_key.codes && *prefix_key.codes == *candidate_key.codes));
			};
			bool predicted_hit = same_prefix_construction();
			double core_estimate = predicted_hit ? suffix_estimates[int(task.script_kind)] + prefix_clone_seconds : core_estimates[int(task.script_kind)];
			double post_estimate = 0, tail_estimate = 0;
			auto predict_tail = [&](const char *stage) {
				log_assert(post.budget.resyn_limit > 0 && post.budget.resub_limit > 0);
				log_assert(post.budget.resyn >= 0 && post.budget.resyn <= post.budget.resyn_limit);
				log_assert(post.budget.resub >= 0 && post.budget.resub <= post.budget.resub_limit);
				double resyn_ratio = double(post.budget.resyn) / post.budget.resyn_limit;
				double resub_ratio = baseline_post.resub_work ? std::min(1.0, double(post.budget.resub_allowance()) / baseline_post.resub_work) : 0;
				post_estimate = baseline_post.predict(post.budget);
				tail_estimate = core_estimate + post_estimate;
				log_debug("opt_fsm_lut4: candidate wall prediction stage=%s construction=%s script=%s carry_mode=%s core estimate=%.9f post estimate=%.9f total estimate=%.9f seconds shared resyn remaining=%lld/%lld resub remaining=%lld/%lld SAT remaining=%lld/4000000 resyn ratio=%.9f resub ratio=%.9f elapsed=%.9f deadline=%.9f seconds.\n",
					stage, task.construction, sequential ? "sequential" : Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic",
					core_estimate, post_estimate, tail_estimate, (long long)post.budget.resyn, (long long)post.budget.resyn_limit,
					(long long)post.budget.resub, (long long)post.budget.resub_limit, (long long)post.budget.sat, resyn_ratio, resub_ratio,
					std::chrono::duration<double>(FsmLimits::Clock::now() - budget.started).count(), deadline_seconds);
				log_debug("opt_fsm_lut4: candidate published post prediction resub local=%lld carry reserved=%lld global=%lld truth remaining=%lld setup seconds=%.9f search seconds=%.9f.\n",
					(long long)post.budget.resub_allowance(), (long long)post.budget.carry_allowance(), (long long)post.budget.resub,
					(long long)(post.budget.truth_limit - post.budget.truth_work), Lut4Mapping::PostTiming::seconds(baseline_post.carry_setup()),
					Lut4Mapping::PostTiming::seconds(baseline_post.carry_search));
			};
			predict_tail("before-construction");
			auto exclude = [&](const char *reason, FsmLimitKind kind) {
				log("opt_fsm_lut4: excluded construction=%s script=%s carry_mode=%s status=LimitReached reason=%s reserved estimate=%lld work remaining=%lld live reservations=%lld memory limit=%lld core estimate=%.9f post estimate=%.9f tail estimate=%.9f elapsed=%.9f deadline=%.9f seconds.\n",
					 task.construction, sequential ? "sequential" : Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic", reason,
					(long long)estimate, (long long)budget.work, (long long)budget.bytes, (long long)budget.memory,
					core_estimate, post_estimate, tail_estimate, std::chrono::duration<double>(FsmLimits::Clock::now() - budget.started).count(), deadline_seconds);
				if (kind == FsmLimitKind::Memory) skipped.memory++;
				else if (kind == FsmLimitKind::Deadline) skipped.deadline++;
				else { skipped.work++; if (!sequential && task.script_kind == Lut4Mapping::ScriptKind::CascadeArea) skipped.cascade_work++; }
				budget.reserved_work = 0;
			};
			if (!budget.time_available(tail_estimate)) { exclude("complete tail deadline reservation", FsmLimitKind::Deadline); continue; }
			if (!budget.begin(estimate)) {
				if (budget.bytes > budget.memory) exclude("memory reservation", FsmLimitKind::Memory);
				else exclude("mapping work reservation", FsmLimitKind::Work);
				continue;
			}
			FsmStorage candidate_storage(budget);
			int64_t mapping_workspace = sequential ? capacity_add(capacity_mul(baseline_abc.nodes, 32), capacity_mul(baseline_abc.wires, 16)) : Lut4Mapping::mapping_workspace(task.script_kind, baseline_abc.nodes, baseline_abc.wires);
			log_debug("opt_fsm_lut4: candidate reservation construction=%s script=%s carry_mode=%s ABC fixed=%lld ABC network=%lld full work estimate=%lld tail estimate=%.6f elapsed=%.6f deadline=%.6f seconds.\n",
				 task.construction, sequential ? "sequential" : Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic",
				(long long)(sequential ? 0 : Lut4Mapping::mapping_fixed_workspace(task.script_kind)),
				(long long)(baseline_abc.nodes * 32 + baseline_abc.wires * 16), (long long)estimate,
				tail_estimate, std::chrono::duration<double>(FsmLimits::Clock::now() - budget.started).count(), deadline_seconds);
			int64_t candidate_capacity = std::max(source_capacity, design_capacity(best.get()));
			int64_t mandatory_phase = std::max(capacity_add(candidate_capacity, capacity_add(helper_workspace, mapping_workspace)),
				capacity_add(source_mux_index, 16 * 1048576));
			auto candidate_memory_request = [&]() {
				int64_t available = std::max<int64_t>(0, budget.memory - budget.bytes - candidate_capacity);
				int64_t resyn_phase = post_phase_capacity(post_index, Lut4Mapping::post_resyn_workspace, available);
				int64_t resub_phase = post_phase_capacity(resub_index, Lut4Mapping::post_resub_workspace, available);
				int64_t carry_phase = post.budget.carry_allowance() ? post_phase_capacity(carry_index, carry_workspace, available) : 0;
				int64_t phase_peak = std::max({mandatory_phase, resyn_phase, resub_phase, carry_phase});
				int64_t reservation = capacity_add(candidate_capacity, phase_peak);
				log_debug("opt_fsm_lut4: candidate memory reservation resident=%lld live=%lld memory=%lld available=%lld mandatory phase=%lld resyn index=%lld resyn workspace=%lld resub index=%lld resub workspace=%lld maximum phase=%lld total=%lld bytes.\n",
					(long long)candidate_capacity, (long long)budget.bytes, (long long)budget.memory, (long long)available,
					(long long)mandatory_phase, (long long)post_index, (long long)(resyn_phase - post_index),
					(long long)resub_index, (long long)(resub_phase - resub_index), (long long)phase_peak, (long long)reservation);
				log_debug("opt_fsm_lut4: candidate carry memory index=%lld workspace=%lld phase=%lld bytes.\n",
					(long long)(carry_phase ? carry_index : 0), (long long)(carry_phase ? carry_phase - carry_index : 0), (long long)carry_phase);
				return reservation;
			};
			int64_t candidate_reservation = candidate_memory_request();
			if (prefix_cache && candidate_reservation > budget.memory - budget.bytes) {
				evict_prefix("candidate admission"); predicted_hit = false;
				candidate_reservation = candidate_memory_request();
				core_estimate = core_estimates[int(task.script_kind)];
				predict_tail("after-cache-eviction");
				if (!budget.time_available(tail_estimate)) { exclude("uncached complete tail deadline reservation", FsmLimitKind::Deadline); continue; }
			}
			if (!candidate_storage.reserve(candidate_reservation)) { exclude("memory candidate and maximum phase reservation", FsmLimitKind::Memory); continue; }
			candidate_storage.resize_required(source_capacity);
			budget.reserved_work -= construction_work;
			if (!budget.spend_mapping(construction_work)) { exclude("construction work reservation", FsmLimitKind::Work); continue; }
			auto candidate = clone_design(design);
			std::vector<FsmEmissionPlan> emissions(models.size());
			FsmStorage emission_storage(budget);
			FsmProofResult result {FsmProofStatus::Proved, "original design construction"};
			if (task.codes) {
				log_assert(task.codes->size() == models.size());
				if (!budget.time_available()) result = {FsmProofStatus::LimitReached, "coordinator deadline"};
				else if (!expand_state_roms(candidate.get(), budget)) result = {FsmProofStatus::LimitReached, budget.limit_reason};
				if (result.proved()) Pass::call(candidate.get(), "fsm -nomap -norecode");
				for (int i = 0; result.proved() && i < GetSize(models); i++) {
					result = apply_model(candidate.get(), models[i], task.codes->at(i), budget, emissions[i], emission_storage,
						task.use_best ? &best_emissions.at(i) : nullptr);
					log_debug("opt_fsm_lut4: candidate state proof construction=%s script=%s carry_mode=%s model=%s.%s status=%s reason=%s.\n",
						task.construction, sequential ? "sequential" : Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic",
						log_id(models[i].module), log_id(models[i].cell), result.name(), result.reason);
				}
				if (result.proved()) Pass::call(candidate.get(), "opt_clean");
			}
			if (!result.proved()) {
				budget.reserved_work = 0;
				log("opt_fsm_lut4: excluded unproved construction=%s script=%s carry_mode=%s status=%s reason=%s, analysis work remaining=%lld, SAT remaining=%lld, workspace=%lld.\n",
					task.construction, sequential ? "sequential" : Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic", result.name(), result.reason,
					(long long)budget.analysis_work, (long long)budget.sat, (long long)budget.bytes);
				continue;
			}
			for (auto &emission : emissions) if (task.codes) log_assert(emission.proved);
			if (task.codes) {
				int64_t emission_capacity = capacity_mul(emissions.capacity(), sizeof(FsmEmissionPlan));
				for (auto &emission : emissions) emission_capacity = capacity_add(emission_capacity, emission.capacity());
				if (!key_storage.reserve(emission_capacity)) { exclude("memory candidate proof identity reservation", FsmLimitKind::Memory); continue; }
				candidate_key.emissions = emissions;
			}
			key_storage.resize_required(candidate_key.capacity());
			candidate_storage.resize_required(design_capacity(candidate.get()));
			bool prefix_hit = !sequential && prefix_cache && prefix_key == candidate_key;
			double clone_seconds = 0;
			FsmLimits::Clock::duration reuse_duration {};
			if (prefix_hit) {
				int64_t clone_capacity = design_capacity(prefix_cache.get());
				int64_t clone_work = prefix_proxy(clone_capacity);
				int64_t metadata_work = 64 + int64_t(prefix_cache->scratchpad.size()) * 8;
				bool retain = clone_capacity <= budget.memory - budget.bytes + candidate_storage.bytes && clone_work <= budget.work - budget.reserved_work;
				if (retain || metadata_work <= budget.work - budget.reserved_work) {
					auto clone_start = FsmLimits::Clock::now();
					if (retain) {
						candidate.reset(); candidate_storage.resize_required(0);
						FsmStorage clone_storage(budget);
						log_assert(clone_storage.reserve(clone_capacity));
						log_assert(budget.spend_mapping(clone_work));
						auto replacement = clone_design(prefix_cache.get());
						candidate = std::move(replacement);
						clone_storage.resize_required(0);
						candidate_storage.resize_required(design_capacity(candidate.get()));
					} else {
						log_assert(budget.spend_mapping(metadata_work));
						candidate.reset();
						candidate_storage.resize_required(0);
						candidate = std::move(prefix_cache);
						prefix_key = {}; prefix_storage.resize_required(0);
						candidate_storage.resize_required(design_capacity(candidate.get()));
						Lut4Mapping::clear_products(candidate.get());
					}
					reuse_duration = FsmLimits::Clock::now() - clone_start;
					clone_seconds = Lut4Mapping::PostTiming::seconds(reuse_duration);
					prefix_clone_seconds = clone_seconds;
					log_debug("opt_fsm_lut4: prefix cache %s construction=%s prefix seconds=%.9f clone/transfer seconds=%.9f capacity=%lld bytes charged proxy=%lld.\n",
						retain ? "hit" : "consume", task.construction, prefix_seconds, clone_seconds, (long long)clone_capacity,
						(long long)(retain ? clone_work : metadata_work));
				} else {
					prefix_hit = false;
					log_debug("opt_fsm_lut4: prefix cache capacity not admitted construction=%s reason=mapping work allowance clone proxy=%lld transfer proxy=%lld.\n",
						task.construction, (long long)clone_work, (long long)metadata_work);
				}
			}
			if (budget.bytes > budget.memory) evict_prefix("constructed candidate admission");
			if (budget.bytes > budget.memory) { exclude("memory constructed Design reservation", FsmLimitKind::Memory); continue; }
			core_estimate = prefix_hit ? suffix_estimates[int(task.script_kind)] : core_estimates[int(task.script_kind)];
			predict_tail("after-construction");
			if (!budget.time_available(tail_estimate)) { exclude("constructed candidate complete tail deadline", FsmLimitKind::Deadline); continue; }
			for (auto &previous : attempted)
				if (same_task(previous.task, task) && previous.emissions == emissions) duplicate = true;
			if (duplicate) {
				budget.reserved_work = 0;
				log_debug("opt_fsm_lut4: reused complete construction identity=%s script=%s carry_mode=%s.\n",
					task.construction, Lut4Mapping::script_name(task.script_kind), task.native ? "native" : "generic");
				continue;
			}
			int64_t identity_bytes = capacity_add(task.construction.capacity(), capacity_mul(emissions.capacity(), sizeof(FsmEmissionPlan)));
			for (auto &emission : emissions) identity_bytes = capacity_add(identity_bytes, emission.capacity());
			if (!pool_storage.reserve(identity_bytes)) { exclude("memory complete construction identity reservation", FsmLimitKind::Memory); continue; }
			log_assert(attempted.size() < attempted.capacity() && GetSize(attempted) < budget.mappings);
			attempted.push_back({task, emissions});
			account_pool();
			if (budget.bytes > budget.memory) evict_prefix("complete identity admission");
			if (budget.bytes > budget.memory) {
				attempted.pop_back(); account_pool();
				exclude("memory complete construction identity reservation", FsmLimitKind::Memory); continue;
			}
			if (!budget.time_available(tail_estimate)) {
				attempted.pop_back(); account_pool();
				exclude("complete construction identity deadline", FsmLimitKind::Deadline); continue;
			}
			map(candidate.get(), task.script_kind, task.construction, task.native, candidate_key, prefix_hit,
				candidate_storage, mapping_workspace, false, reuse_duration);
			if (!last_mapping_success) {
				attempted.pop_back(); account_pool();
				if (budget.limit_kind == FsmLimitKind::Deadline) skipped.deadline++;
				else skipped.memory++;
				continue;
			}
			auto cost = candidate_cost;
			optional_completed = true;
			complete_generic(cost, baseline.second);
			candidate_storage.resize_required(design_capacity(candidate.get()));
			log("opt_fsm_lut4: mapped candidate LUT4=%lld DFF=%lld, original LUT4=%lld DFF=%lld.\n", (long long)cost.first, (long long)cost.second, (long long)baseline.first, (long long)baseline.second);
			if (cost.first < best_cost.first && cost.second <= baseline.second) {
				best = std::move(candidate); best_cost = cost;
				post.select(best.get());
				best_task = task; best_task.use_best = false;
				best_emissions = std::move(emissions);
				int64_t emission_bytes = emission_storage.bytes;
				emission_storage.resize_required(0); best_emission_storage.resize_required(emission_bytes);
				candidate_storage.resize_required(0);
				design_storage.resize_required(source_capacity + design_capacity(best.get()));
			}
		}
		if (feedback_enabled && !feedback_attempted) feedback();
		complete();
	}
} OptFsmLut4Pass;

PRIVATE_NAMESPACE_END
