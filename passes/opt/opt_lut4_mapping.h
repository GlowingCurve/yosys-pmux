#ifndef YOSYS_OPT_LUT4_MAPPING_H
#define YOSYS_OPT_LUT4_MAPPING_H

#include "kernel/yosys.h"
#include "kernel/cellaigs.h"
#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/sigtools.h"
#include "frontends/ast/ast.h"
#include "frontends/verilog/preproc.h"

#include <array>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <memory>
#include <regex>
#include <functional>
#include <set>

YOSYS_NAMESPACE_BEGIN
namespace Lut4Mapping {

constexpr int max_full_mappings = 8;
constexpr int64_t post_resyn_work_limit = 16000000, post_resub_work_limit = 100000000, post_sat_limit = 4000000;
constexpr int64_t post_resyn_workspace = 64 * 1048576, post_resub_workspace = 32 * 1048576;
constexpr int64_t post_carry_work_limit = 24000000, post_truth_limit = 4000000, post_carry_workspace = 96 * 1048576;

inline int64_t capacity_add(int64_t left, int64_t right) {
	if (left < 0 || right < 0 || left > INT64_MAX - right)
		log_error("opt_lut4_mapping: capacity addition overflow.\n");
	return left + right;
}
inline int64_t capacity_mul(int64_t left, int64_t right) {
	if (left < 0 || right < 0 || (right && left > INT64_MAX / right))
		log_error("opt_lut4_mapping: capacity multiplication overflow.\n");
	return left * right;
}

enum class MappingPhase { Prefix, Arithmetic, Abc, Post, Lookup, Resyn, Resub, Carry, Idle };
inline const char *phase_name(MappingPhase phase) {
	switch (phase) {
	case MappingPhase::Prefix: return "prefix";
	case MappingPhase::Arithmetic: return "arithmetic";
	case MappingPhase::Abc: return "abc";
	case MappingPhase::Post: return "post";
	case MappingPhase::Lookup: return "lookup";
	case MappingPhase::Resyn: return "resyn";
	case MappingPhase::Resub: return "resub";
	case MappingPhase::Carry: return "carry";
	case MappingPhase::Idle: return "idle";
	}
	log_error("opt_lut4_mapping: invalid mapping phase.\n");
}

// 共用 Mux 区间的实测费用仅在当前 synth 调用内传递。
struct CommonMuxContext {
	using Clock = std::chrono::steady_clock;
	Design *design;
	Clock::duration duration {};
	bool measured = false;
	CommonMuxContext *previous;
	static CommonMuxContext *&active() { static CommonMuxContext *value = nullptr; return value; }
	explicit CommonMuxContext(Design *design) : design(design), previous(active()) { active() = this; }
	~CommonMuxContext() { active() = previous; }
	CommonMuxContext(const CommonMuxContext &) = delete;
	CommonMuxContext &operator=(const CommonMuxContext &) = delete;
	static void record(Design *design, Clock::duration duration) {
		auto context = active();
		if (!context || context->design != design) return;
		log_assert(!context->measured && duration >= Clock::duration::zero());
		context->duration = duration; context->measured = true;
	}
	static Clock::duration measured_duration(Design *design) {
		auto context = active();
		return context && context->design == design && context->measured ? context->duration : Clock::duration::zero();
	}
};

// 阶段预留跟随真实执行区间，回调保留协调器的对象所有权。
struct PhaseContext {
	Design *design;
	std::function<bool(MappingPhase)> enter;
	std::function<void()> observe;
	std::function<bool(Design *)> admit_clone;
	std::function<void()> finish_clone;
	void *audit_owner = nullptr;
	PhaseContext *previous;
	bool failed = false;
	MappingPhase phase = MappingPhase::Idle;
	int64_t post_credit = 0;
	static PhaseContext *&active() { static PhaseContext *value = nullptr; return value; }
	PhaseContext(Design *design, std::function<bool(MappingPhase)> enter, std::function<void()> observe) :
		design(design), enter(std::move(enter)), observe(std::move(observe)), previous(active()) { active() = this; }
	~PhaseContext() { active() = previous; }
	static bool begin(Design *design, MappingPhase phase) {
		auto context = active();
		if (!context || context->design != design) return true;
		if (context->failed) return false;
		context->phase = phase;
		if (!context->enter(phase)) { context->failed = true; return false; }
		return true;
	}
	static void account() { auto context = active(); if (context && context->observe) context->observe(); }
};

inline std::string post_key(const char *kind, const char *field) {
	return std::string("opt_lut4_post.") + kind + "." + field;
}

inline bool shared_post(Design *design) { return design->scratchpad_get_bool("opt_lut4_post.shared"); }

// 工作与 SAT 额度通过候选 scratchpad 传递，全部模块使用同一余额。
inline void report_post(Design *design, const char *kind, int64_t work, int64_t sat, int64_t peak) {
	log_assert(work >= 0 && sat >= 0 && peak >= 0);
	for (auto item : {std::make_pair("work", work), std::make_pair("sat", sat)}) {
		auto key = post_key(kind, item.first);
		design->scratchpad_set_string(key, std::to_string(std::stoll(design->scratchpad_get_string(key, "0")) + item.second));
	}
	auto peak_key = post_key(kind, "peak");
	design->scratchpad_set_string(peak_key, std::to_string(std::max<int64_t>(peak, std::stoll(design->scratchpad_get_string(peak_key, "0")))));
	if (shared_post(design)) {
		for (auto item : {std::make_pair("remaining", work), std::make_pair("sat_remaining", sat)}) {
			auto key = post_key(kind, item.first);
			int64_t remaining = std::stoll(design->scratchpad_get_string(key));
			log_assert(item.second <= remaining);
			design->scratchpad_set_string(key, std::to_string(remaining - item.second));
		}
	}
	log_debug("opt_lut4_post: pass=%s cumulative work=%s SAT=%s workspace peak=%s bytes.\n", kind,
		design->scratchpad_get_string(post_key(kind, "work")), design->scratchpad_get_string(post_key(kind, "sat")),
		design->scratchpad_get_string(peak_key));
}

inline void reset_post_report(Design *design, const char *kind) {
	for (const char *field : {"work", "sat", "truth", "peak"}) design->scratchpad_set_string(post_key(kind, field), "0");
}

inline int64_t carry_scale(Design *design) {
	int64_t result = 0;
	for (auto module : design->selected_unboxed_modules()) for (auto cell : module->cells())
		if (cell->type.in(ID($lut), ID($not), ID($_NOT_))) result++;
	return result;
}

inline int64_t carry_index_bytes(Module *module) {
	int64_t result = capacity_add(2 * 1048576 + 2048, capacity_mul(1536, module->cells_size()));
	for (auto cell : module->cells()) for (auto &port : cell->connections())
		result = capacity_add(result, capacity_mul(384, GetSize(port.second)));
	for (auto wire : module->wires()) result = capacity_add(result, capacity_mul(256, wire->width));
	return result;
}

inline int64_t carry_index_work(Module *module) {
	int64_t result = capacity_mul(32, module->cells_size());
	for (auto cell : module->cells()) for (auto &port : cell->connections()) result = capacity_add(result, capacity_mul(8, GetSize(port.second)));
	for (auto wire : module->wires()) result = capacity_add(result, wire->width);
	return result;
}

inline void report_carry(Design *design, int64_t work, int64_t truth, int64_t peak) {
	log_assert(work >= 0 && truth >= 0 && peak >= 0);
	for (auto item : {std::make_pair("work", work), std::make_pair("truth", truth)}) {
		auto key = post_key("carry", item.first);
		design->scratchpad_set_string(key, std::to_string(capacity_add(std::stoll(design->scratchpad_get_string(key, "0")), item.second)));
	}
	auto peak_key = post_key("carry", "peak");
	design->scratchpad_set_string(peak_key, std::to_string(std::max(peak, int64_t(std::stoll(design->scratchpad_get_string(peak_key, "0"))))));
	if (shared_post(design)) for (auto item : {std::make_pair("remaining", work), std::make_pair("truth_remaining", truth)}) {
		auto key = post_key("carry", item.first);
		int64_t remaining = std::stoll(design->scratchpad_get_string(key));
		log_assert(item.second <= remaining);
		design->scratchpad_set_string(key, std::to_string(remaining - item.second));
	}
	log_debug("opt_lut4_post: pass=carry work=%lld truth=%lld workspace peak=%lld bytes.\n", (long long)work, (long long)truth, (long long)peak);
}

inline int64_t post_index_bytes(Module *module, bool cell_indexes) {
	int64_t result = 0;
	for (auto wire : module->wires()) result = capacity_add(result, capacity_mul(128, wire->width));
	if (cell_indexes) {
		result = capacity_add(result, capacity_mul(512, module->cells_size()));
		for (auto cell : module->cells()) for (auto &port : cell->connections()) result = capacity_add(result, capacity_mul(192, GetSize(port.second)));
	}
	return result;
}

inline int64_t post_setup_work(Module *module, int64_t allowance, int64_t &inspection, int64_t *index_work = nullptr) {
	inspection = 0;
	if (index_work) *index_work = 64 * int64_t(module->cells_size());
	auto spend = [&](int64_t work) {
		if (work > allowance - inspection) return false;
		inspection += work; return true;
	};
	if (!spend(64)) return -1;
	int64_t result = 64 + 8 * int64_t(module->wires_size()) + 16 * int64_t(module->cells_size());
	for (auto wire : module->wires()) {
		if (!spend(8)) return -1;
		result += 32 * int64_t(wire->width);
	}
	for (auto cell : module->cells()) {
		if (!spend(16)) return -1;
		for (auto &port : cell->connections()) {
			if (!spend(8)) return -1;
			result += 8 * int64_t(GetSize(port.second));
			if (index_work) *index_work += 8 * int64_t(GetSize(port.second));
		}
	}
	for (auto &connection : module->connections()) {
		if (!spend(8)) return -1;
		result += 8 * int64_t(GetSize(connection.first) + GetSize(connection.second));
	}
	return result;
}

inline std::map<IdString, Module *> post_modules(Design *design) {
	std::map<IdString, Module *> modules;
	std::vector<Module *> pending = design->selected_unboxed_modules();
	while (!pending.empty()) {
		auto module = pending.back(); pending.pop_back();
		if (!modules.emplace(module->name, module).second) continue;
		for (auto cell : module->cells()) {
			auto dependency = design->module(cell->type);
			if (dependency && !modules.count(dependency->name)) pending.push_back(dependency);
		}
	}
	return modules;
}

enum class ScriptKind { AreaLutpack, CascadeArea, RewriteRefactor, ExpandedCuts, FeedbackBoolean, Count };
constexpr size_t script_kind_count = size_t(ScriptKind::Count);

inline const char *script_name(ScriptKind kind)
{
	switch (kind) {
	case ScriptKind::AreaLutpack: return "area-lutpack";
	case ScriptKind::CascadeArea: return "cascade-area";
	case ScriptKind::RewriteRefactor: return "rewrite-refactor";
	case ScriptKind::ExpandedCuts: return "expanded-cuts";
	case ScriptKind::FeedbackBoolean: return "feedback-boolean";
	case ScriptKind::Count: break;
	}
	log_error("opt_abc9_area: invalid script kind.\n");
}

inline ScriptKind parse_script_kind(const std::string &name)
{
	for (auto kind : {ScriptKind::AreaLutpack, ScriptKind::CascadeArea, ScriptKind::RewriteRefactor, ScriptKind::ExpandedCuts, ScriptKind::FeedbackBoolean})
		if (name == script_name(kind)) return kind;
	log_cmd_error("opt_abc9_area: unknown script family '%s'.\n", name);
}

inline std::string script(ScriptKind kind, int64_t source_cells, int wire_delay)
{
	std::string result = "+&put;strash;";
	if (kind == ScriptKind::FeedbackBoolean)
		return result + "balance;resub,-K,6,-N,2,-M,1,-F,0,-l,-v;rewrite;refactor,-N,8,-M,1,-C,16;balance;"
			"resub,-K,8,-N,2,-M,1,-F,0,-l,-v;rewrite;rewrite,-z;balance;refactor,-N,8,-M,0,-C,16,-z;rewrite,-z;balance;"
			"dch,-f,-W,4,-C,100,-S,1000;if,-K,4,-a,-C,8,-F,1,-A,2,-m,-W,300;"
			"lutpack,-N,3,-Q,1,-S,2,-L,10,-s;mfs2,-a,-W,1,-F,8,-D,64,-M,64,-L,10,-C,500;&get,-m;echo,opt_abc9_area_complete";
	if (kind == ScriptKind::RewriteRefactor)
		result += "balance;rewrite;refactor,-N,8,-M,1;rewrite,-z;balance;";
	result += "dch,-f,-W,4,-C,100,-S,1000;";
	int cuts = kind == ScriptKind::AreaLutpack || kind == ScriptKind::CascadeArea ? 8 : kind == ScriptKind::RewriteRefactor ? 12 : source_cells > 20000 ? 12 : 16;
	bool expanded = kind == ScriptKind::ExpandedCuts;
	result += stringf("if,-K,4,-a,-C,%d,-F,%d,-A,%d,%s-W,%d;", cuts, expanded ? 2 : 1, expanded ? 3 : 2, expanded ? "" : "-m,", wire_delay);
	if (kind == ScriptKind::CascadeArea) {
		result += "mfs2,-a,-W,1,-F,8,-D,64,-M,64,-L,10,-C,500;";
		result += "lutpack,-N,4,-Q,3,-S,2,-L,10,-z,-s,-v;";
		result += "mfs2,-a,-W,1,-F,8,-D,64,-M,64,-L,10,-C,500;";
	} else {
		result += "lutpack,-N,3,-Q,1,-S,2,-L,0,-s;";
		result += expanded ? "mfs2,-a,-W,2,-F,12,-D,64,-M,96,-L,0,-C,750;" : "mfs2,-a,-W,1,-F,8,-D,20,-M,64,-L,0,-C,500;";
	}
	return result + "&get,-m;echo,opt_abc9_area_complete";
}

inline int64_t mapping_effort(ScriptKind kind, int64_t effort)
{
	log_assert(effort >= 0 && effort <= INT64_MAX / 3);
	if (kind == ScriptKind::CascadeArea) return effort * 3;
	if (kind == ScriptKind::RewriteRefactor) return effort + effort / 2;
	if (kind == ScriptKind::ExpandedCuts) return effort * 2;
	if (kind == ScriptKind::FeedbackBoolean) return effort * 2;
	return effort;
}

// 固定数组、真值表及 BDD 节点按本地 LPK 分配计算；动态网络另行估计。
inline int64_t mapping_fixed_workspace(ScriptKind kind)
{
	int variables = kind == ScriptKind::CascadeArea ? 13 : 10;
	int64_t truth_bytes = int64_t(1) << (variables - 3);
	int64_t truth_entries = 1024 + 64 + 4096 + 2 * variables;
	int64_t cuts = 10000 * int64_t((5 + 2 * 100) * sizeof(uint32_t) + sizeof(int32_t));
	int64_t truths = truth_entries * (sizeof(void *) + truth_bytes) + 32 * truth_bytes;
	int64_t bdd_nodes = 32768 * int64_t(2 * sizeof(uint32_t) + 2 * sizeof(void *));
	int64_t result = cuts + truths + bdd_nodes + 256 * 1024;
	if (kind == ScriptKind::FeedbackBoolean) {
		// resub 使用八变量真值、150 个 divisor 和最多 500 个配对容器。
		result = capacity_add(result, 151 * 32 + (11 * 150 + 8 * 500) * int64_t(sizeof(void *)));
		// refactor 的局部真值、ISOP/BDD 与固定整数容器独立预留。
		result = capacity_add(result, capacity_add(2 * bdd_nodes, 4 * 65536));
	}
	return result;
}

inline int64_t mapping_workspace(ScriptKind kind, const int64_t nodes, const int64_t wires)
{
	log_assert(nodes >= 0 && wires >= 0);
	int64_t network = capacity_add(capacity_mul(nodes, 32), capacity_mul(wires, 16));
	if (kind == ScriptKind::FeedbackBoolean) {
		// rewrite 的 cut manager 保留每个节点至多 250 个四变量 cut。
		int64_t cut_entry = 2 * int64_t(sizeof(void *)) + 8 * int64_t(sizeof(uint32_t));
		network = capacity_add(network, capacity_mul(nodes, capacity_add(capacity_mul(250, cut_entry), 128)));
	}
	return capacity_add(mapping_fixed_workspace(kind), network);
}

inline void clear_products(Design *design)
{
	for (const char *key : {"abc9_ops.prep_bypass.did_something", "abc9_ops.prep_dff_submod.did_something",
		"abc9_ops.lut_library", "abc9_ops.box_library", "write_xaiger.num_ands", "write_xaiger.num_wires",
		"write_xaiger.num_inputs", "write_xaiger.num_outputs", "read_aiger.inputs", "read_aiger.outputs", "read_aiger.co_count",
		"opt_fsm_lut4.completed", "opt_fsm_lut4.evaluating", "opt_lut4_mapping.evaluating", "opt_lut4_mapping.script_kind", "opt_lut4_mapping.carry_mode"})
		design->scratchpad_unset(key);
}

// Selection 内容保持完整，查询模块时使用保存或接收这些选集的 Design。
inline void rebind_selections(Design *design, std::vector<RTLIL::Selection> &selection,
	dict<IdString, RTLIL::Selection> &variables)
{
	for (auto &item : selection) item.current_design = design;
	for (auto &item : variables) item.second.current_design = design;
}

inline void rebind_selections(Design *design)
{
	rebind_selections(design, design->selection_stack, design->selection_vars);
}

inline std::unique_ptr<Design> clone_design(Design *source)
{
	if (!source->bindings_.empty()) log_error("opt_lut4_mapping: Design bindings cannot be cloned.\n");
	auto result = std::make_unique<Design>();
	result->flagBufferedNormalized = source->flagBufferedNormalized;
	for (auto module : source->modules()) {
		if (!module->bindings_.empty()) log_error("opt_lut4_mapping: module %s contains bindings.\n", module);
		result->add(module->clone());
	}
	for (auto &node : source->verilog_packages) result->verilog_packages.push_back(node->clone());
	for (auto &node : source->verilog_globals) result->verilog_globals.push_back(node->clone());
	result->verilog_defines->merge(*source->verilog_defines);
	result->scratchpad = source->scratchpad;
	clear_products(result.get());
	result->scratchpad_set_bool("abc9.verify", true);
	result->selection_stack = source->selection_stack;
	result->selection_vars = source->selection_vars;
	result->selected_active_module = source->selected_active_module;
	rebind_selections(result.get());
	return result;
}

// 回调只在当前完整候选内有效，Design 身份不依赖可被 Pass 重建的模块。
struct PrefixContext {
	using Clock = std::chrono::steady_clock;
	Design *design;
	std::function<void(Design *, Clock::duration)> capture;
	Clock::time_point started;
	Clock::duration duration {};
	bool measured = false;
	PrefixContext *previous;
	static PrefixContext *&active() { static PrefixContext *context = nullptr; return context; }
	PrefixContext(Design *design, std::function<void(Design *, Clock::duration)> capture) :
		design(design), capture(std::move(capture)), previous(active()) { active() = this; }
	~PrefixContext() { active() = previous; }
	PrefixContext(const PrefixContext &) = delete;
	PrefixContext &operator=(const PrefixContext &) = delete;
	static void begin(Design *design) {
		auto context = active();
		if (!context || context->design != design) return;
		log_assert(!context->measured);
		context->started = Clock::now();
	}
	static void complete(Design *design) {
		auto context = active();
		if (!context || context->design != design) return;
		log_assert(!context->measured);
		context->duration = Clock::now() - context->started;
		context->measured = true;
		if (context->capture) context->capture(design, context->duration);
	}
};

// 通用 checkpoint 在当前完整候选内捕获，缓存复用的 primitive Design 不进入回调。
struct GenericCheckpointContext {
	Design *design;
	std::function<void(Design *)> capture;
	GenericCheckpointContext *previous;
	static GenericCheckpointContext *&active() { static GenericCheckpointContext *value = nullptr; return value; }
	GenericCheckpointContext(Design *design, std::function<void(Design *)> capture) :
		design(design), capture(std::move(capture)), previous(active()) { active() = this; }
	~GenericCheckpointContext() { active() = previous; }
	GenericCheckpointContext(const GenericCheckpointContext &) = delete;
	GenericCheckpointContext &operator=(const GenericCheckpointContext &) = delete;
	static void complete(Design *design, bool reused) {
		auto context = active();
		if (context && context->design == design && !reused && context->capture) context->capture(design);
	}
};

// 已完成准备的反馈候选通过类型化作用域进入 map_luts:check。
struct FeedbackContinuation {
	Design *design;
	FeedbackContinuation *previous;
	static FeedbackContinuation *&active() { static FeedbackContinuation *value = nullptr; return value; }
	explicit FeedbackContinuation(Design *design) : design(design), previous(active()) { active() = this; }
	~FeedbackContinuation() { active() = previous; }
	FeedbackContinuation(const FeedbackContinuation &) = delete;
	FeedbackContinuation &operator=(const FeedbackContinuation &) = delete;
	static bool matches(Design *design) { auto context = active(); return context && context->design == design; }
};

// 完整模块通过现成 cloneInto 重建其信号所有权。
inline void transfer(Design *target, Design *source)
{
	for (auto module : target->modules().to_vector()) target->remove(module);
	for (auto module : source->modules()) target->add(module->clone());
	rebind_selections(target);
}

struct SavedDesigns {
	const std::array<std::string, 4> names {{"$abc9", "$abc9_map", "$abc9_unmap", "$abc9_holes"}};
	std::map<std::string, Design *> previous;
	SavedDesigns() {
		for (auto &name : names) {
			auto found = saved_designs.find(name);
			if (found != saved_designs.end()) { previous.emplace(name, found->second); saved_designs.erase(found); }
		}
	}
	void check_empty() const {
		for (auto &name : names)
			if (saved_designs.count(name)) log_error("opt_lut4_mapping: ABC9 left temporary design %s.\n", name);
	}
	~SavedDesigns() {
		for (auto &name : names) {
			auto found = saved_designs.find(name);
			if (found != saved_designs.end()) { delete found->second; saved_designs.erase(found); }
		}
		saved_designs.insert(previous.begin(), previous.end());
	}
};

struct StateGuard {
	Design *design;
	std::vector<RTLIL::Selection> selection;
	dict<IdString, RTLIL::Selection> variables;
	dict<std::string, std::string> scratchpad;
	std::string active;
	explicit StateGuard(Design *design) : design(design), selection(design->selection_stack), variables(design->selection_vars),
		scratchpad(design->scratchpad), active(design->selected_active_module) {
		rebind_selections(design, selection, variables);
	}
	~StateGuard() {
		design->selection_stack = std::move(selection); design->selection_vars = std::move(variables);
		design->scratchpad = std::move(scratchpad); design->selected_active_module = std::move(active);
		rebind_selections(design);
	}
};

// ABC9 执行期间保护完整 primitive 边界；普通清理期间恢复用户原始属性。
struct CarryBoundaryGuard {
	// ABC9 的 design -load 重建模块，恢复属性时通过名称查询当前设计。
	struct SavedKeep { IdString module, name; bool present; Const value; };
	Design *design;
	std::vector<SavedKeep> saved;
	explicit CarryBoundaryGuard(Design *design) : design(design) {
		if (!design) return;
		for (auto module : design->selected_modules()) for (auto cell : module->cells()) {
			if (cell->type != ID(cycloneiv_lcell_comb) ||
				(!cell->attributes.count(ID(cycloneiv_carry_chain)) && !cell->get_bool_attribute(ID(cycloneiv_carry_bi)) && !cell->get_bool_attribute(ID(cycloneiv_carry_x)))) continue;
			if (cell->has_keep_attr()) continue;
			auto keep = cell->attributes.find(ID::keep);
			saved.push_back({module->name, cell->name, keep != cell->attributes.end(), keep == cell->attributes.end() ? Const() : keep->second});
			cell->set_bool_attribute(ID::keep);
		}
	}
	~CarryBoundaryGuard() {
		for (auto &item : saved) {
			auto module = design->module(item.module);
			if (!module) log_error("opt_lut4_mapping: protected carry module %s disappeared.\n", item.module);
			auto cell = module->cell(item.name);
			if (!cell || cell->type != ID(cycloneiv_lcell_comb))
				log_error("opt_lut4_mapping: protected carry primitive changed for %s.%s.\n", item.module, item.name);
			if (item.present) cell->attributes[ID::keep] = item.value;
			else cell->attributes.erase(ID::keep);
		}
	}
};

struct ScriptReference {
	ScriptPass *pass;
	ScriptReference() : pass(dynamic_cast<ScriptPass *>(pass_register.at("abc9"))) {
		if (!pass) log_error("opt_lut4_mapping: ABC9 requires ScriptPass.\n");
		pass->active_design = nullptr;
	}
	~ScriptReference() { pass->active_design = nullptr; }
};

struct AuditResult {
	int executions = 0;
	int64_t nodes = 0, wires = 0;
};

// 每个真实网络独立检查执行、完成标记与等价证明。
struct MappingAudit : LogSink {
	struct Network { std::string module; int64_t nodes, wires; int outputs, executions = 0, completions = 0, proofs = 0; };
	std::vector<Network> networks;
	bool require_completion;
	PhaseContext *phase_context = nullptr;
	explicit MappingAudit(bool require_completion = true) : require_completion(require_completion) {
		auto phase = PhaseContext::active();
		if (phase && !phase->audit_owner) { phase_context = phase; phase->audit_owner = this; }
	}
	~MappingAudit() { if (phase_context) phase_context->audit_owner = nullptr; }
	void log(const LogMessage &msg) override {
		if (msg.severity == LogSeverity::Error) return;
		const auto &line = msg.message;
		if (phase_context && (line.find("Executing ABC9_OPS") != std::string::npos || line.find("Executing TECHMAP") != std::string::npos ||
			line.find("Executing WBFLIP") != std::string::npos || line.find("Extracted ") != std::string::npos || line.find("Running ABC command:") != std::string::npos))
			PhaseContext::account();
		static const std::regex extracted("Extracted ([0-9]+) AND gates and ([0-9]+) wires from module `([^']+)' to a netlist network with [0-9]+ inputs and ([0-9]+) outputs\\.");
		std::smatch match;
		if (line.find("Extracted ") != std::string::npos && std::regex_search(line, match, extracted))
			networks.push_back({match[3].str(), std::stoll(match[1].str()), std::stoll(match[2].str()), std::stoi(match[4].str())});
		if (line.find("Running ABC command:") != std::string::npos) {
			if (networks.empty()) log_error("opt_lut4_mapping: ABC execution without an extracted network.\n");
			networks.back().executions++;
		}
		if (line.find("ABC:") == std::string::npos) return;
		std::string lower = line;
		for (auto &ch : lower) ch = std::tolower(static_cast<unsigned char>(ch));
		for (const char *failure : {"error", "failed", "failure", "not equivalent", "undecided", "unknown command",
			"cannot", "usage:", "empty network", "original network is restored"})
			if (lower.find(failure) != std::string::npos) log_error("opt_lut4_mapping: ABC9 command failed: %s", line);
		if (networks.empty()) return;
		if (line.find("ABC: opt_abc9_area_complete") != std::string::npos) networks.back().completions++;
		if (line.find("Networks are equivalent") != std::string::npos) networks.back().proofs++;
	}
	AuditResult finish() const {
		AuditResult result;
		for (auto &network : networks) {
			int expected = network.outputs ? 1 : 0;
			if (network.executions != expected || network.proofs != expected || (require_completion && network.completions != expected))
				log_error("opt_lut4_mapping: incomplete ABC9 execution or proof for %s.\n", network.module);
			result.executions += network.executions; result.nodes += network.nodes; result.wires += network.wires;
		}
		return result;
	}
};

inline bool boundary(Cell *cell, Design *design) {
	return cell->has_keep_attr() || cell->is_builtin_ff() || cell->is_mem_cell() || (!yosys_celltypes.cell_known(cell->type) && design->module(cell->type));
}

inline bool user_boundary_attributes(const dict<IdString, Const> &attributes) {
	for (auto &item : attributes)
		if (!item.first.in(ID::src, ID::hdlname, ID::keep, ID(unused_bits))) return true;
	return false;
}

struct Metrics { int64_t luts = 0, inverters = 0; int64_t area() const { return luts + inverters; } };
inline Metrics metrics(Design *design) {
	Metrics result;
	for (auto module : design->selected_modules()) for (auto cell : module->cells()) {
		if (cell->type == ID($lut)) {
			int width = cell->getParam(ID::WIDTH).as_int();
			if (width < 0 || width > 4 || GetSize(cell->getPort(ID::A)) != width || GetSize(cell->getPort(ID::Y)) != 1 || GetSize(cell->getParam(ID::LUT)) != (1 << width))
				log_error("opt_lut4_mapping: invalid LUT4 in %s.%s.\n", module, cell);
			result.luts++;
		} else if (cell->type.in(ID($not), ID($_NOT_))) result.inverters += GetSize(cell->getPort(ID::Y));
		else if (!boundary(cell, design)) log_error("opt_lut4_mapping: incomplete mapping in %s.%s (%s).\n", module, cell, cell->type);
	}
	return result;
}

inline void normalize_output_aliases(Design *design)
{
	RTLIL::Selection selection(false);
	bool needed = false;
	for (auto module : design->selected_modules()) {
		SigMap sigmap(module);
		dict<SigBit, std::vector<Cell *>> drivers;
		for (auto cell : module->cells())
			if (cell->type == ID($lut) && !cell->has_keep_attr())
				for (auto bit : sigmap(cell->getPort(ID::Y))) if (bit.wire) drivers[bit].push_back(cell);
		for (auto &entry : drivers) if (GetSize(entry.second) > 1) {
			needed = true;
			for (auto cell : entry.second) selection.select(module, cell);
		}
	}
	if (!needed) return;
	// ABC9 重复输出别名的 LUT 使用现成真值函数规范化和完全相同函数合并。
	Pass::call_on_selection(design, selection, "opt_lut_ins");
	Pass::call_on_selection(design, selection, "opt_merge");
}

// 复用同一 Design 上已存在的外层审计，独立调用时建立本地审计。
inline void map_one(Design *design, ScriptKind kind, int wire_delay = 300, const std::string &executable = {})
{
	StateGuard state(design); SavedDesigns saved;
	CarryBoundaryGuard carry_boundaries(design);
	// simplemap 将高层组合单元转换为 ABC9 能直接保留的原生 keep 单元。
	for (auto module : design->selected_modules()) {
		for (auto cell : module->cells().to_vector()) {
			if (!cell->has_keep_attr() || cell->is_builtin_ff() || cell->is_mem_cell() || cell->type.in(ID($_AND_), ID($_NOT_)) || Aig(cell).name.empty()) continue;
			auto attributes = cell->attributes; auto name = cell->name;
			pool<IdString> previous;
			for (auto existing : module->cells()) previous.insert(existing->name);
			RTLIL::Selection selection(false); selection.select(module, cell);
			Pass::call_on_selection(design, selection, "simplemap");
			if (module->cell(name)) log_error("opt_abc9_area: kept cell %s.%s requires techmap before ABC9.\n", module, name);
			for (auto emitted : module->cells()) if (!previous.count(emitted->name)) emitted->attributes = attributes;
		}
	}
	int64_t source_cells = 0;
	for (auto module : design->selected_modules()) {
		if (!design->selected_whole_module(module) || module->has_processes() || module->has_memories())
			log_error("opt_abc9_area: selected module %s requires proc and memory mapping.\n", module);
		for (auto cell : module->cells()) {
			if (cell->type == ID($lut) && !cell->has_keep_attr()) log_error("opt_abc9_area: expected unmapped logic in %s.%s.\n", module, cell);
			if (!boundary(cell, design) && Aig(cell).name.empty()) log_error("opt_abc9_area: unsupported unmapped cell %s.%s (%s); run techmap first.\n", module, cell, cell->type);
		}
		source_cells += module->cells_size();
	}
	clear_products(design);
	design->scratchpad_set_bool("abc9.verify", true);
	design->scratchpad_set_bool("abc9.dff", false);
	std::string commands = script(kind, source_cells, wire_delay);
	std::vector<std::string> args {"abc9", "-lut", "4", "-W", std::to_string(wire_delay), "-script", commands};
	if (!executable.empty()) { args.push_back("-exe"); args.push_back(executable); }
	{
		ScriptReference reference; LogManager::Scoped scoped(logger());
		auto phase = PhaseContext::active();
		if (phase && phase->design == design && phase->audit_owner) {
			// 同一Design的外层审计由它自己的出口完成汇总与检查。
			Pass::call(design, args);
		} else {
			auto &audit = logger().add_sink<MappingAudit>();
			log("opt_abc9_area: single-map candidate=%s source_cells=%lld ABC fixed workspace estimate=%lld script=%s\n", script_name(kind), (long long)source_cells, (long long)mapping_fixed_workspace(kind), commands);
			Pass::call(design, args); audit.finish();
		}
	}
	saved.check_empty();
	normalize_output_aliases(design);
}

struct MappingBudget {
	int mappings = max_full_mappings, completed_mappings = 0, abc_executions = 0;
	int64_t work = 8000000, actual_work = 0, reserved_work = 0, peak_reserved_work = 0;
	int64_t bytes = 0, peak_bytes = 0, memory = 64 * 1048576;
	int64_t raw_mapping_work = 0;
	int64_t aig_nodes = 0, aig_wires = 0;
	bool spend(int64_t amount) { log_assert(amount >= 0); if (amount > work - reserved_work) return false; work -= amount; actual_work += amount; return true; }
	bool reserve(int64_t amount) { log_assert(amount >= 0); if (amount > memory - bytes) return false; bytes += amount; peak_bytes = std::max(bytes, peak_bytes); return true; }
	void reserve_required(int64_t amount) { bytes = capacity_add(bytes, amount); peak_bytes = std::max(bytes, peak_bytes); }
	bool begin(int64_t estimate, bool required = false) {
		log_assert(!reserved_work && estimate >= 0);
		if (!required && (completed_mappings >= mappings || estimate > work || bytes > memory)) return false;
		reserved_work = estimate; peak_reserved_work = std::max(peak_reserved_work, reserved_work); return true;
	}
	void finish(const AuditResult &abc, int64_t cells, ScriptKind kind, bool sequential = false) {
		log_assert(cells >= 0);
		int64_t raw_effort = cells * 64 + abc.nodes * 256 + abc.wires * 32;
		int64_t effort = sequential ? raw_effort : mapping_effort(kind, raw_effort);
		int64_t estimate = reserved_work; reserved_work = 0;
		raw_mapping_work += raw_effort;
		actual_work += effort; work = std::max<int64_t>(0, work - effort);
		completed_mappings++; abc_executions += abc.executions; aig_nodes += abc.nodes; aig_wires += abc.wires;
		log("opt_fsm_lut4: script=%s mapping proxy effort=%lld, charged=%lld, reserved=%lld, AIG nodes=%lld, AIG wires=%lld, mapped cells=%lld, ABC executions=%d, cumulative raw mapping proxy=%lld, cumulative charged work=%lld, remaining=%lld.\n",
			sequential ? "sequential" : script_name(kind), (long long)raw_effort, (long long)effort, (long long)estimate, (long long)abc.nodes, (long long)abc.wires, (long long)cells, abc.executions, (long long)raw_mapping_work, (long long)actual_work, (long long)work);
	}
};

struct PostBudget {
	int64_t resyn = post_resyn_work_limit, resub = post_resub_work_limit, sat = post_sat_limit;
	int64_t resyn_limit = post_resyn_work_limit, resub_limit = post_resub_work_limit, scale = 0;
	int64_t resyn_work = 0, resub_work = 0, sat_work = 0, peak = 0;
	int64_t carry_work = 0, truth_work = 0, lut_scale = 0, truth_limit = 0;
	bool carry_enabled = true;
	int64_t carry_allowance() const {
		return carry_enabled && truth_work < truth_limit ? std::min(resub, std::min(post_carry_work_limit, capacity_mul(lut_scale, 8192))) : 0;
	}
	int64_t resub_allowance() const { return resub - carry_allowance(); }
	void size(Design *design) {
		lut_scale = carry_scale(design);
		truth_limit = std::max(truth_limit, std::min(post_truth_limit, capacity_mul(lut_scale, 2048)));
		int64_t nodes = 0;
		CellTypes types(design);
		for (auto module : design->selected_unboxed_modules()) {
			SigMap sigmap(module); pool<SigBit> outputs;
			for (auto wire : module->wires()) if (wire->port_output)
				for (auto bit : SigSpec(wire)) if (sigmap(bit).wire) outputs.insert(sigmap(bit));
			for (auto cell : module->cells()) {
				if (cell->type == ID($lut)) nodes++;
				else if (cell->type.in(ID($not), ID($_NOT_))) nodes += GetSize(cell->getPort(ID::Y));
				else for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
					for (auto bit : port.second) if (sigmap(bit).wire) outputs.insert(sigmap(bit));
			}
			nodes += outputs.size();
		}
		if (scale && nodes <= scale) return;
		scale = std::max<int64_t>(1, nodes);
		resyn_limit = std::min(post_resyn_work_limit, capacity_mul(scale, 300000));
		resub_limit = std::min(post_resub_work_limit, capacity_mul(scale, 400000));
		resyn = std::max<int64_t>(0, resyn_limit - resyn_work);
		resub = std::max<int64_t>(0, resub_limit - resub_work - carry_work);
		log_debug("opt_lut4_post: network scale=%lld LUT/inverter nodes and distinct effective outputs, design limits resyn=%lld resub=%lld SAT=4000000; linear work per node=300000/400000, caps=16000000/100000000.\n",
			(long long)scale, (long long)resyn_limit, (long long)resub_limit);
	}
	void publish(Design *design, int64_t memory) const {
		log_assert(memory >= 0);
		design->scratchpad_set_bool("opt_lut4_post.shared", true);
		design->scratchpad_set_string(post_key("resyn", "remaining"), std::to_string(resyn));
		design->scratchpad_set_string(post_key("resyn", "sat_remaining"), "0");
		int64_t carry = carry_allowance(), ordinary = resub - carry;
		design->scratchpad_set_string(post_key("resub", "remaining"), std::to_string(ordinary));
		design->scratchpad_set_string(post_key("resub", "published"), std::to_string(ordinary));
		design->scratchpad_set_string(post_key("resub", "sat_remaining"), std::to_string(sat));
		design->scratchpad_set_string(post_key("carry", "remaining"), std::to_string(carry));
		design->scratchpad_set_string(post_key("carry", "published"), std::to_string(carry));
		design->scratchpad_set_string(post_key("carry", "scale"), std::to_string(lut_scale));
		design->scratchpad_set_string(post_key("carry", "truth_remaining"), std::to_string(truth_limit - truth_work));
		design->scratchpad_set_string("opt_lut4_post.memory_remaining", std::to_string(memory));
		reset_post_report(design, "resyn"); reset_post_report(design, "resub"); reset_post_report(design, "carry");
		log_debug("opt_lut4_post: published resyn remaining=%lld, resub local=%lld carry reserved=%lld global remaining=%lld, SAT remaining=%lld truth remaining=%lld.\n",
			(long long)resyn, (long long)ordinary, (long long)carry, (long long)resub, (long long)sat, (long long)(truth_limit - truth_work));
	}
	void collect(Design *design, MappingBudget &mapping) {
		auto read = [&](const char *kind, const char *field) { return std::stoll(design->scratchpad_get_string(post_key(kind, field), "0")); };
		int64_t rw = read("resyn", "work"), sw = read("resub", "work"), ss = read("resub", "sat");
		int64_t rp = read("resub", "published");
		int64_t cw = read("carry", "work"), ct = read("carry", "truth"), cp = read("carry", "published");
		log_assert(rp + cp == resub && rw <= resyn && sw <= rp && ss <= sat && cw <= cp && ct <= truth_limit - truth_work);
		log_assert(read("resub", "remaining") == rp - sw);
		log_assert(read("carry", "remaining") == cp - cw && read("carry", "truth_remaining") == truth_limit - truth_work - ct);
		resyn -= rw; resub -= sw + cw; sat -= ss;
		log_assert(resyn == read("resyn", "remaining") && sat == read("resub", "sat_remaining"));
		resyn_work += rw; resub_work += sw; sat_work += ss;
		carry_work += cw; truth_work += ct;
		int64_t workspace = std::max({read("resyn", "peak"), read("resub", "peak"), read("carry", "peak")});
		peak = std::max(peak, workspace);
		mapping.peak_bytes = std::max(mapping.peak_bytes, mapping.bytes + workspace);
		log_debug("opt_lut4_post: design cumulative resyn=%lld/%lld resub=%lld/%lld SAT=%lld/4000000 workspace peak=%lld bytes, live designs and cache=%lld bytes.\n",
			(long long)resyn_work, (long long)resyn_limit, (long long)resub_work, (long long)resub_limit, (long long)sat_work, (long long)peak, (long long)mapping.bytes);
		log_debug("opt_lut4_post: carry cumulative work=%lld truth=%lld/%lld resub global used=%lld/%lld remaining=%lld.\n",
			(long long)carry_work, (long long)truth_work, (long long)truth_limit,
			(long long)(resub_work + carry_work), (long long)resub_limit, (long long)resub);
		design->scratchpad_unset("opt_lut4_post.shared");
	}
};

// 身份数据直接来自 RTLIL 图；每个 token 保存完整字段，比较不使用散列。
struct StructureKey {
	std::vector<std::string> fields;
	bool valid = true;
	int64_t bytes() const {
		return capacity_add(sizeof(*this), dynamic_bytes());
	}
	int64_t dynamic_bytes() const {
		int64_t result = capacity_mul(fields.capacity(), sizeof(std::string));
		for (auto &field : fields) result = capacity_add(result, capacity_add(field.capacity(), 1));
		return result;
	}
	bool operator==(const StructureKey &other) const { return valid && other.valid && fields == other.fields; }
};

inline StructureKey mapped_structure(Design *design, const std::string &configuration, int64_t limit,
	bool normalize_logic = true, bool complete_design = false) {
	StructureKey key;
	int64_t payload = 0;
	auto add = [&](const std::string &value) {
		if (!key.valid) return;
		payload += 2 * (sizeof(std::string) + int64_t(value.size()) + 1);
		if (payload > limit) { key.valid = false; return; }
		key.fields.push_back(value);
	};
	auto number = [&](int64_t value) { add(std::to_string(value)); };
	auto constant = [&](const Const &value) {
		number(value.flags); number(GetSize(value));
		std::string states; states.reserve(GetSize(value));
		for (auto bit : value) states.push_back(char('0' + int(bit)));
		add(states);
	};
	auto values = [&](const dict<IdString, Const> &items) {
		std::map<IdString, Const> ordered(items.begin(), items.end());
		number(ordered.size());
		for (auto &item : ordered) { add(item.first.str()); constant(item.second); }
	};
	add(configuration);
	auto modules = post_modules(design);
	if (complete_design) for (auto module : design->modules()) modules[module->name] = module;
	number(modules.size());
	for (auto &entry : modules) {
		if (!key.valid) break;
		auto module = entry.second;
		if (module->has_processes() || module->has_memories() || !module->bindings_.empty()) { key.valid = false; break; }
		add(module->name.str()); values(module->attributes); values(module->parameter_default_values);
		std::set<IdString> available(module->avail_parameters.begin(), module->avail_parameters.end());
		number(available.size()); for (auto name : available) add(name.str());
		number(module->ports.size()); for (auto name : module->ports) add(name.str());
		bool normalize = normalize_logic && design->selected(module) && !module->get_blackbox_attribute();
		number(normalize);
		SigMap sigmap(module); CellTypes types(design);
		std::map<IdString, Wire *> wires;
		std::map<IdString, Cell *> fixed;
		dict<SigBit, std::vector<std::string>> anchors;
		dict<SigBit, Cell *> drivers;
		pool<Cell *> combinational;
		for (auto wire : module->wires()) wires.emplace(wire->name, wire);
		for (auto &item : wires) {
			auto wire = item.second;
			if (normalize && !wire->port_id && wire->attributes.empty() && wire->name.str()[0] == '$') continue;
			for (int bit = 0; bit < wire->width; bit++) if (wire->port_input || !normalize) {
				auto signal = sigmap(SigBit(wire, bit));
				if (!anchors.count(signal)) anchors[signal] = {"wire", wire->name.str(), std::to_string(bit)};
			}
		}
		for (auto cell : module->cells()) {
			bool comb = normalize && !boundary(cell, design) && cell->type.in(ID($lut), ID($_NOT_), ID($not)) &&
				cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) == 1;
			if (comb) {
				auto bit = sigmap(cell->getPort(ID::Y)).as_bit();
				if (!bit.wire || drivers.count(bit) || anchors.count(bit)) { key.valid = false; break; }
				drivers[bit] = cell; combinational.insert(cell);
			} else {
				fixed.emplace(cell->name, cell);
				for (auto &port : cell->connections()) if (normalize && types.cell_output(cell->type, port.first))
					for (int bit = 0; bit < GetSize(port.second); bit++) {
						auto signal = sigmap(port.second[bit]);
						if (anchors.count(signal)) { key.valid = false; break; }
						anchors[signal] = {"cell", cell->name.str(), port.first.str(), std::to_string(bit)};
					}
			}
		}
		dict<Cell *, int> visited;
		pool<Cell *> visiting;
		std::function<void(SigBit)> signal;
		auto ports = [&](Cell *cell) {
			std::map<IdString, SigSpec> ordered(cell->connections().begin(), cell->connections().end());
			number(ordered.size());
			for (auto &port : ordered) {
				add(port.first.str()); number(GetSize(port.second));
				for (auto bit : port.second) signal(bit);
			}
		};
		signal = [&](SigBit bit) {
			if (!key.valid) return;
			bit = sigmap(bit);
			if (!bit.wire) { add("constant"); number(int(bit.data)); return; }
			if (!normalize) { add("wire"); add(bit.wire->name.str()); number(bit.offset); return; }
			if (anchors.count(bit)) { add("anchor"); number(anchors.at(bit).size()); for (auto &field : anchors.at(bit)) add(field); return; }
			if (!drivers.count(bit)) {
				if (bit.wire->name.str()[0] == '$' && bit.wire->attributes.empty()) { key.valid = false; return; }
				add("undriven"); add(bit.wire->name.str()); number(bit.offset); return;
			}
			auto cell = drivers.at(bit);
			if (visiting.count(cell)) { key.valid = false; return; }
			if (visited.count(cell)) { add("reference"); number(visited.at(cell)); return; }
			int id = visited.size(); visited[cell] = id; visiting.insert(cell);
			add("node"); number(id); add(cell->type.str()); values(cell->parameters); values(cell->attributes);
			add(cell->name.str()[0] == '$' ? "temporary" : cell->name.str());
			// Y 为当前节点的定义；输入端口严格保存原次序。
			std::map<IdString, SigSpec> inputs;
			for (auto &port : cell->connections()) if (port.first != ID::Y) inputs.emplace(port.first, port.second);
			number(inputs.size());
			for (auto &port : inputs) { add(port.first.str()); number(GetSize(port.second)); for (auto input : port.second) signal(input); }
			visiting.erase(cell);
		};
		int wire_count = 0;
		for (auto &item : wires) if (!normalize || item.second->port_id || !item.second->attributes.empty() || item.first.str()[0] != '$') wire_count++;
		number(wire_count);
		for (auto &item : wires) {
			auto wire = item.second;
			if (normalize && !wire->port_id && wire->attributes.empty() && wire->name.str()[0] == '$') continue;
			add(wire->name.str()); number(wire->width); number(wire->start_offset); number(wire->upto); number(wire->is_signed);
			number(wire->port_id); number(wire->port_input); number(wire->port_output); values(wire->attributes);
			for (auto bit : SigSpec(wire)) signal(bit);
		}
		number(fixed.size());
		for (auto &item : fixed) { add(item.first.str()); add(item.second->type.str()); values(item.second->parameters); values(item.second->attributes); ports(item.second); }
		if (normalize && visited.size() != combinational.size()) key.valid = false;
		if (!normalize) {
			number(module->connections().size());
			for (auto &connection : module->connections()) {
				number(GetSize(connection.first)); for (auto bit : connection.first) { add(bit.wire ? bit.wire->name.str() : ""); number(bit.wire ? bit.offset : int(bit.data)); }
				number(GetSize(connection.second)); for (auto bit : connection.second) { add(bit.wire ? bit.wire->name.str() : ""); number(bit.wire ? bit.offset : int(bit.data)); }
			}
		}
	}
	return key;
}

struct PostContext;
inline PostContext *&active_post_context() { static PostContext *context = nullptr; return context; }

enum class PostPhase { Complete, Lookup, Resyn, Resub, Carry, ResynSearch, ResubSearch, CarrySearch };

struct PostTiming {
	using Clock = std::chrono::steady_clock;
	Clock::time_point started, finished;
	Clock::duration complete {}, lookup {}, resyn {}, resub {}, carry {}, resyn_search {}, resub_search {}, carry_search {};
	bool measured = false;
	int64_t resub_work = 0, carry_work = 0;
	Clock::duration carry_setup() const { log_assert(carry_search <= carry); return carry - carry_search; }
	Clock::duration resyn_setup() const { log_assert(resyn_search <= resyn); return resyn - resyn_search; }
	Clock::duration resub_setup() const { log_assert(resub_search <= resub); return resub - resub_search; }
	Clock::duration cleanup() const {
		log_assert(measured && lookup + resyn + resub + carry <= complete);
		return complete - lookup - resyn - resub - carry;
	}
	static double seconds(Clock::duration duration) { return std::chrono::duration<double>(duration).count(); }
	double predict(const PostBudget &budget) const {
		double ordinary_ratio = resub_work ? std::min(1.0, double(budget.resub_allowance()) / resub_work) : 0;
		double carry_ratio = carry_work ? std::min(1.0, double(budget.carry_allowance()) / carry_work) : 0;
		return seconds(lookup + cleanup()) +
			(budget.resyn ? seconds(resyn_setup()) + seconds(resyn_search) * double(budget.resyn) / budget.resyn_limit : 0) +
			(budget.resub_allowance() ? seconds(resub_setup()) + seconds(resub_search) * ordinary_ratio : 0) +
			(budget.carry_allowance() ? seconds(carry_setup()) + seconds(carry_search) * carry_ratio : 0);
	}
};

struct PostContext {
	struct Entry { StructureKey key; int64_t lut, dff; };
	MappingBudget &mapping;
	PostBudget budget;
	std::string configuration;
	std::vector<Entry> entries;
	StructureKey pending;
	Design *best = nullptr;
	int best_entry = -1, matched = -1;
	int64_t accounted_bytes = 0;
	Design *mapping_design = nullptr;
	PostTiming timing;
	int64_t starting_resub_work = 0, starting_carry_work = 0;
	PostContext *previous;
	explicit PostContext(MappingBudget &mapping, std::string configuration) : mapping(mapping), configuration(std::move(configuration)), previous(active_post_context()) {
		int64_t entry_bytes = capacity_mul(mapping.mappings, sizeof(Entry));
		mapping.reserve_required(entry_bytes); entries.reserve(mapping.mappings); mapping.bytes -= entry_bytes;
		active_post_context() = this; account();
		log_debug("opt_lut4_post: structure cache entry capacity=%lld mapping allowance=%d reservation=%lld bytes.\n",
			(long long)entries.capacity(), mapping.mappings, (long long)capacity_mul(entries.capacity(), sizeof(Entry)));
	}
	~PostContext() { mapping.bytes -= accounted_bytes; log_assert(mapping.bytes >= 0); active_post_context() = previous; }
	int64_t bytes() const {
		int64_t result = capacity_add(sizeof(*this), capacity_add(capacity_mul(entries.capacity(), sizeof(Entry)), capacity_add(configuration.capacity(), pending.dynamic_bytes())));
		for (auto &entry : entries) result = capacity_add(result, entry.key.dynamic_bytes());
		return result;
	}
	void account() {
		int64_t current = bytes();
		mapping.bytes += current - accounted_bytes; accounted_bytes = current;
		mapping.peak_bytes = std::max(mapping.peak_bytes, mapping.bytes);
	}
	void begin(Design *design, bool baseline) {
		log_assert(!mapping_design);
		mapping_design = design; timing = {};
		starting_resub_work = budget.resub_work;
		starting_carry_work = budget.carry_work;
		pending = {}; pending.valid = false; matched = -1;
		account();
		design->scratchpad_set_bool("opt_lut4_post.baseline", baseline);
		budget.publish(design, baseline ? post_resyn_workspace : std::max<int64_t>(0, mapping.memory - mapping.bytes));
	}
	bool lookup(Design *design) {
		auto phase = PhaseContext::active();
		int64_t credit = phase && phase->design == design ? phase->post_credit : 0;
		int64_t index = 0;
		for (auto module : design->selected_unboxed_modules()) index = std::max(index, post_index_bytes(module, true));
		if (phase && phase->design == design && credit < index) return false;
		collect(design);
		budget.size(design);
		publish(design);
		int64_t graph = 0;
		for (auto &entry : post_modules(design)) {
			auto module = entry.second;
			graph = capacity_add(graph, capacity_add(capacity_mul(512, module->cells_size()), capacity_mul(256, module->wires_size())));
			for (auto wire : module->wires()) graph = capacity_add(graph, capacity_mul(128, wire->width));
		}
		int64_t available = std::min(capacity_add(mapping.memory, credit) - mapping.bytes - graph, mapping.memory - mapping.bytes);
		if (available <= 0) return false;
		int64_t temporary = capacity_add(available, std::max<int64_t>(0, graph - credit));
		if (!mapping.reserve(temporary)) return false;
		pending = mapped_structure(design, configuration, available);
		mapping.bytes -= temporary;
		account();
		mapping.peak_bytes = std::max(mapping.peak_bytes, capacity_add(mapping.bytes, std::max<int64_t>(0, graph - credit)));
		if (!pending.valid || capacity_add(mapping.bytes, std::max<int64_t>(0, graph - credit)) > mapping.memory) { pending = {}; pending.valid = false; account(); return false; }
		publish(design);
		for (int i = 0; i < GetSize(entries); i++) if (pending == entries[i].key) {
			matched = i;
			log("opt_lut4_post: exact mapped structure cache hit entry=%d LUT4=%lld DFF=%lld result=%s.\n", i,
				(long long)entries[i].lut, (long long)entries[i].dff, i == best_entry ? "best complete design" : "completed candidate");
			if (i == best_entry) {
				log_assert(best);
				if (phase && phase->design == design && phase->admit_clone && !phase->admit_clone(best)) return false;
				// 当前活跃模块及其实际依赖复用完整结果，其他模块保持当前候选内容。
				for (auto &entry : post_modules(best)) {
					auto existing = design->module(entry.first);
					if (existing) design->remove(existing);
					design->add(entry.second->clone());
				}
				if (phase && phase->design == design && phase->finish_clone) phase->finish_clone();
				return true;
			}
			// 已完成结果已经包含所有正收益替换，当前原始网络仍然合法。
			for (const char *kind : {"resyn", "resub", "carry"})
				design->scratchpad_set_string(post_key(kind, "remaining"), "0");
			return false;
		}
		return false;
	}
	void collect(Design *design) {
		log_assert(mapping_design == design);
		if (!shared_post(design)) return;
		if (matched >= 0 && matched != best_entry) {
			for (const char *kind : {"resyn", "resub", "carry"})
				for (const char *field : {"work", "sat", "truth"})
					log_assert(design->scratchpad_get_string(post_key(kind, field), "0") == "0");
			design->scratchpad_set_string(post_key("resyn", "remaining"), std::to_string(budget.resyn));
			design->scratchpad_set_string(post_key("resub", "remaining"), design->scratchpad_get_string(post_key("resub", "published")));
			design->scratchpad_set_string(post_key("carry", "remaining"), design->scratchpad_get_string(post_key("carry", "published")));
		}
		auto phase = PhaseContext::active();
		int64_t credit = phase && phase->design == design ? phase->post_credit : 0;
		mapping.bytes -= credit;
		budget.collect(design, mapping);
		mapping.bytes = capacity_add(mapping.bytes, credit);
	}
	void publish(Design *design) {
		// 下一阶段发布额度之前，结算上一阶段尚未收集的实际消费。
		collect(design);
		auto phase = PhaseContext::active();
		int64_t credit = phase && phase->design == design ? phase->post_credit : 0;
		budget.publish(design, design->scratchpad_get_bool("opt_lut4_post.baseline") ?
			(phase && phase->phase == MappingPhase::Carry ? credit : post_resyn_workspace) :
			std::max<int64_t>(0, capacity_add(mapping.memory, credit) - mapping.bytes));
		if (matched >= 0 && matched != best_entry) {
			for (const char *kind : {"resyn", "resub", "carry"})
				design->scratchpad_set_string(post_key(kind, "remaining"), "0");
		}
	}
	void finish(Design *design, int64_t lut, int64_t dff) {
		log_assert(mapping_design == design && timing.measured);
		timing.cleanup();
		if (matched >= 0 && matched != best_entry) log_assert(lut >= entries[matched].lut && dff == entries[matched].dff);
		collect(design);
		timing.resub_work = budget.resub_work - starting_resub_work;
		timing.carry_work = budget.carry_work - starting_carry_work;
		if (pending.valid && matched < 0) {
			log_assert(GetSize(entries) < mapping.mappings && entries.size() < entries.capacity());
			matched = entries.size(); entries.push_back({std::move(pending), lut, dff});
		}
		pending = {}; pending.valid = false;
		account();
		mapping_design = nullptr;
	}
	void cancel(Design *design) {
		collect(design);
		pending = {}; pending.valid = false; matched = -1;
		account(); mapping_design = nullptr;
	}
	void select(Design *design) { best = design; best_entry = matched; }
};

// 实际计时通过当前候选的类型化接口传递，完整区间包含缓存复用及全部相关清理。
struct PostTimer {
	PostContext *context = nullptr;
	PostPhase phase;
	PostTiming::Clock::time_point started;
	PostTimer(Design *design, PostPhase phase) : phase(phase) {
		if (!design) return;
		context = active_post_context();
		if (!context || context->mapping_design != design)
			log_error("opt_lut4_post: missing active mapping timing context.\n");
		started = PostTiming::Clock::now();
	}
	PostTimer(const PostTimer &) = delete;
	PostTimer &operator=(const PostTimer &) = delete;
	~PostTimer() {
		if (!context) return;
		auto finished = PostTiming::Clock::now();
		auto duration = finished - started;
		auto &timing = context->timing;
		switch (phase) {
		case PostPhase::Complete:
			log_assert(!timing.measured);
			timing.started = started; timing.finished = finished;
			timing.complete = duration; timing.measured = true; break;
		case PostPhase::Lookup: timing.lookup += duration; break;
		case PostPhase::Resyn: timing.resyn += duration; break;
		case PostPhase::Resub: timing.resub += duration; break;
		case PostPhase::Carry: timing.carry += duration; break;
		case PostPhase::ResynSearch: timing.resyn_search += duration; break;
		case PostPhase::ResubSearch: timing.resub_search += duration; break;
		case PostPhase::CarrySearch: timing.carry_search += duration; break;
		}
	}
};

inline Design *timed_post_design(Design *design) {
	auto context = active_post_context();
	return context && context->mapping_design == design ? design : nullptr;
}

inline bool reuse_post_result(Design *design) {
	if (!shared_post(design)) return false;
	auto context = active_post_context();
	if (!context) log_error("opt_lut4_post: missing design-level coordinator.\n");
	return context->lookup(design);
}

}
YOSYS_NAMESPACE_END
#endif
