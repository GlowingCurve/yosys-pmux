#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include <map>
#include <limits>
#include <charconv>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum TV : int8_t { T0, T1, TD };

using CellSet = pool<Cell *, hashlib::hash_ptr_ops>;
template<typename T> using CellMap = dict<Cell *, T, hashlib::hash_ptr_ops>;

struct Limits {
	int leaves = 10, cells = 64, rows = 4096, nodes = 131072;
	int64_t work = 40000000;
};

// 原结构与候选结构共用逐位表达式，每个内部节点实际发射一个 LUT4。
struct Expr {
	SigBit bit;
	std::vector<int> args;
	unsigned table = 0;
	bool leaf = true;
};

struct BitPlan {
	int d = -1, en = -1;
	bool replace_ce = false;
	bool constant = false;
	bool unused = false;
	std::vector<int> shape;
};

struct Plan {
	Cell *ff = nullptr;
	std::vector<BitPlan> bits;
	CellSet dead;
	dict<SigBit, int> delta;
	pool<int> added;
	int64_t removed = 0, cost = 0;
};

struct BitNode {
	std::vector<int> slots, sel;
};

struct BoundaryInfo {
	dict<SigBit, bool> safe_bits;
	CellMap<bool> safe_cells, safe_ffs;
	dict<IdString, bool> safe_cell_names, safe_ff_names;
	pool<IdString> state_names, protected_names;
	CellMap<pool<SigBit>> dependencies;
	pool<SigBit> barriers;
	int64_t items = 0;
};

struct IndexedSignal {
	Cell *owner = nullptr;
	SigBit bit;
	IdString identity;
};

struct ReshapeWorker {
	Module *module;
	ConstEval ce;
	SigMap &sigmap;
	FfInitVals initvals;
	Limits limits;
	bool force, exhausted = false;
	int64_t work = 0;
	int accepted = 0, rejected = 0, unsafe = 0;
	int64_t saved_items = 0;
	int64_t attribute_bytes = 0;
	dict<SigBit, std::pair<Cell *, int>> drivers;
	pool<SigBit> ambiguous, protected_bits;
	pool<SigBit> discarded_q;
	CellSet protected_cells, retired, state_cells;
	BoundaryInfo boundary;
	dict<SigBit, int> users, ff_data_users;
	dict<SigBit, int> input_drivers;
	CellMap<std::vector<SigBit>> cell_inputs, cell_outputs;
	CellMap<IdString> original_names;
	std::vector<Expr> exprs;
	dict<SigBit, int> leaf_ids;
	std::map<std::pair<std::vector<int>, unsigned>, int> expr_ids;
	dict<int, SigBit> emitted;
	dict<int, IndexedSignal> existing_functions;
	dict<SigBit, IndexedSignal> data_aliases;
	pool<int> committed;
	std::vector<Plan> plans;
	using MergeKey = std::pair<SigSpec, std::vector<std::pair<IdString, Const>>>;
	using FinalMergeKey = std::pair<MergeKey, std::pair<int, int>>;
	std::map<FinalMergeKey, IndexedSignal> ff_representatives;
	dict<SigBit, SigBit> ff_groups, equivalent_q;
	pool<SigBit> group_members;
	CellMap<CellSet> ff_neighbors;
	dict<SigBit, BitPlan> fixed_group_bits;
	pool<SigBit> state_groups;
	CellSet analyzed;
	bool group_mode = false, prefer_enable = false;
	int group_ce_mode = -1;

	std::vector<BitNode> cone;
	dict<SigBit, int> cone_ids;
	pool<SigBit> visiting;
	std::vector<SigBit> sources, ctrl;
	dict<SigBit, int> source_ids, ctrl_ids;
	int en_slot = -1, reset_slot = -1;
	bool cone_bad = false;

	ReshapeWorker(Module *m, Limits l, bool f) : module(m), ce(m), sigmap(ce.assign_map), limits(l), force(f)
	{
		initvals.set(&sigmap, module);
		// 驱动、连接出现次数、端口和别名保护属性只建立一次。
		for (auto wire : module->wires()) {
			bool protect = wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep);
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) { ambiguous.insert(bit); input_drivers[bit]++; }
				if (protect) protected_bits.insert(bit);
				if (wire->port_output || protect) users[bit]++;
			}
		}
		for (auto cell : module->cells()) {
			original_names[cell] = cell->name;
			if (StaticCellTypes::categories.is_ff(cell->type) || cell->type == ID($anyinit)) state_cells.insert(cell);
			if (state_cells.count(cell)) boundary.state_names.insert(cell->name);
			bool protect = cell->get_bool_attribute(ID::keep) || cell->get_bool_attribute(ID::lut_keep);
			if (protect || !cell->known()) protected_cells.insert(cell);
			if (protect || !cell->known()) boundary.protected_names.insert(cell->name);
			for (auto &conn : cell->connections()) {
				SigSpec sig = sigmap(conn.second);
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sig) {
						cell_inputs[cell].push_back(bit);
						if (bit.wire) users[bit]++;
					}
				if (cell->known() && cell->output(conn.first))
					for (int i = 0; i < GetSize(sig); i++) {
						auto bit = sig[i];
						cell_outputs[cell].push_back(bit);
						if (drivers.count(bit)) ambiguous.insert(bit);
						else drivers[bit] = std::make_pair(cell, i);
						if (protect) protected_bits.insert(bit);
					}
				if (!cell->known()) for (auto bit : sig) ambiguous.insert(bit);
			}
			if (StaticCellTypes::categories.is_ff(cell->type) && cell->hasPort(ID::D))
				for (auto bit : sigmap(cell->getPort(ID::D))) ff_data_users[bit]++;
		}
		// 输入端口本身可作为叶子，带有内部驱动的输入端口具有多驱动风险。
		for (auto wire : module->wires()) if (wire->port_input)
			for (auto bit : sigmap(wire)) if (!drivers.count(bit) && input_drivers[bit] == 1) ambiguous.erase(bit);
		boundary.barriers = protected_bits;
		for (auto wire : module->wires()) if (wire->attributes.count(ID::init))
			for (auto bit : sigmap(wire))
				if (!drivers.count(bit) || !StaticCellTypes::categories.is_ff(drivers.at(bit).first->type))
					boundary.barriers.insert(bit);
		build_boundaries();
		literal(State::S0);
		literal(State::S1);
	}

	bool spend(int64_t amount)
	{
		log_assert(amount >= 0);
		if (amount > limits.work - work) { exhausted = true; return false; }
		work += amount;
		return true;
	}

	int literal(SigBit bit)
	{
		if (exhausted) return -1;
		if (leaf_ids.count(bit)) return leaf_ids.at(bit);
		if (GetSize(exprs) >= limits.nodes) { exhausted = true; return -1; }
		Expr e;
		e.bit = bit;
		int id = GetSize(exprs);
		exprs.push_back(e);
		leaf_ids[bit] = id;
		return id;
	}

	// 将常量、重复输入、恒等函数和无关输入化简为规范化节点。
	int gate(std::vector<int> args, unsigned table)
	{
		if (exhausted || std::find(args.begin(), args.end(), -1) != args.end()) return -1;
		log_assert(GetSize(args) <= 4);
		if (!spend(64)) return -1;
		std::vector<int> vars;
		for (int id : args)
			if (!(exprs[id].leaf && !exprs[id].bit.wire)) vars.push_back(id);
		std::sort(vars.begin(), vars.end());
		vars.erase(std::unique(vars.begin(), vars.end()), vars.end());
		unsigned result = 0;
		for (int p = 0; p < (1 << GetSize(vars)); p++) {
			int old = 0;
			for (int i = 0; i < GetSize(args); i++) {
				int id = args[i];
				bool v;
				if (exprs[id].leaf && !exprs[id].bit.wire) {
					log_assert(exprs[id].bit == State::S0 || exprs[id].bit == State::S1);
					v = exprs[id].bit == State::S1;
				} else v = (p >> (std::lower_bound(vars.begin(), vars.end(), id) - vars.begin())) & 1;
				if (v) old |= 1 << i;
			}
			if ((table >> old) & 1) result |= 1u << p;
		}
		for (int i = GetSize(vars) - 1; i >= 0; i--) {
			bool needed = false;
			for (int p = 0; p < (1 << GetSize(vars)); p++)
				if (((result >> p) & 1) != ((result >> (p ^ (1 << i))) & 1)) needed = true;
			if (needed) continue;
			unsigned next = 0;
			for (int p = 0; p < (1 << (GetSize(vars) - 1)); p++) {
				int old = (p & ((1 << i) - 1)) | ((p >> i) << (i + 1));
				if ((result >> old) & 1) next |= 1u << p;
			}
			vars.erase(vars.begin() + i);
			result = next;
		}
		if (vars.empty()) return literal(result ? State::S1 : State::S0);
		if (GetSize(vars) == 1 && result == 2) return vars[0];
		auto key = std::make_pair(vars, result);
		auto it = expr_ids.find(key);
		if (it != expr_ids.end()) return it->second;
		if (GetSize(exprs) >= limits.nodes) { exhausted = true; return -1; }
		Expr e;
		e.leaf = false;
		e.args = vars;
		e.table = result;
		int id = GetSize(exprs);
		exprs.push_back(e);
		expr_ids.emplace(key, id);
		return id;
	}

	int mux(int a, int b, int s) { return gate({a, b, s}, 0xca); }

	static int project(int p, const std::vector<int> &support)
	{
		int out = 0;
		for (int i = 0; i < GetSize(support); i++) if ((p >> support[i]) & 1) out |= 1 << i;
		return out;
	}

	int decompose(const std::vector<int> &args, const std::vector<bool> &table)
	{
		if (exhausted || !spend(table.size())) return -1;
		if (GetSize(args) <= 4) {
			unsigned bits = 0;
			for (int p = 0; p < GetSize(table); p++) if (table[p]) bits |= 1u << p;
			return gate(args, bits);
		}
		int half = GetSize(table) / 2;
		std::vector<int> small(args.begin(), args.end() - 1);
		std::vector<bool> low(table.begin(), table.begin() + half), high(table.begin() + half, table.end());
		int a = decompose(small, low), b = decompose(small, high);
		return mux(a, b, args.back());
	}

	// 无关项的选择和最终 Shannon 分解由同一份计划完成。
	int function(const SigSpec &leaves, const std::vector<TV> &table)
	{
		int n = GetSize(leaves);
		if (!spend(int64_t(table.size()) * (n + 1) * (n + 1))) return -1;
		std::vector<int> support;
		for (int i = 0; i < n; i++) support.push_back(i);
		for (int i = n - 1; i >= 0; i--) {
			auto trial = support;
			trial.erase(std::find(trial.begin(), trial.end(), i));
			std::vector<TV> seen(1 << GetSize(trial), TD);
			bool ok = true;
			for (int p = 0; p < GetSize(table); p++) {
				if (table[p] == TD) continue;
				int q = project(p, trial);
				if (seen[q] != TD && seen[q] != table[p]) { ok = false; break; }
				seen[q] = table[p];
			}
			if (ok) support = trial;
		}
		std::vector<bool> full(1 << GetSize(support), false);
		for (int p = 0; p < GetSize(table); p++) if (table[p] == T1) full[project(p, support)] = true;
		std::vector<int> args;
		for (int i : support) args.push_back(literal(leaves[i]));
		return decompose(args, full);
	}

	bool existing(int id)
	{
		return existing_functions.count(id) && valid_index(existing_functions.at(id));
	}

	void gather(int id, pool<int> &nodes, dict<SigBit, int> *refs = nullptr, bool reuse = true)
	{
		log_assert(id >= 0);
		if (exprs[id].leaf) {
			if (refs && exprs[id].bit.wire) (*refs)[exprs[id].bit]++;
			return;
		}
		if (reuse && existing(id)) {
			if (refs) (*refs)[existing_functions.at(id).bit]++;
			return;
		}
		if ((reuse && committed.count(id)) || !nodes.insert(id).second) return;
		for (int a : exprs[id].args) gather(a, nodes, refs, reuse);
	}

	int control(SigBit bit)
	{
		if (bit == State::S0) return -1;
		if (bit == State::S1) return -2;
		if (!bit.wire || ambiguous.count(bit)) { cone_bad = true; return -3; }
		if (ctrl_ids.count(bit)) return ctrl_ids.at(bit);
		if (GetSize(ctrl) >= limits.cells) { cone_bad = true; return -3; }
		int id = GetSize(ctrl);
		ctrl.push_back(bit);
		ctrl_ids[bit] = id;
		return id;
	}

	int source(SigBit bit)
	{
		if (source_ids.count(bit)) return -1 - source_ids.at(bit);
		int id = GetSize(sources);
		sources.push_back(bit);
		source_ids[bit] = id;
		return -1 - id;
	}

	int add_cone(SigBit bit, int depth = 0)
	{
		if (!spend(1)) return source(bit);
		if (visiting.count(bit)) { cone_bad = true; return source(bit); }
		if (cone_ids.count(bit)) return cone_ids.at(bit);
		if (!drivers.count(bit) || ambiguous.count(bit) || boundary.barriers.count(bit)) return source(bit);
		auto driver = drivers.at(bit);
		Cell *cell = driver.first;
		if (!cell->type.in(ID($mux), ID($pmux)) || protected_cells.count(cell) || retired.count(cell) ||
			(depth && users[bit] != 1) || GetSize(cone) >= limits.cells || depth >= limits.cells) return source(bit);
		if (GetSize(cell->getPort(ID::Y)) > 4096 || GetSize(cell->getPort(ID::S)) > limits.cells) return source(bit);
		SigSpec a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
		int width = GetSize(cell->getPort(ID::Y)), offset = driver.second;
		if (offset >= width || GetSize(a) != width || GetSize(b) != width * GetSize(s) ||
			(cell->type == ID($mux) && GetSize(s) != 1) || GetSize(s) > limits.cells) {
			cone_bad = true; return source(bit);
		}
		if (!spend(int64_t(GetSize(a)) + GetSize(b) + GetSize(s))) return source(bit);
		int id = GetSize(cone);
		cone.emplace_back();
		cone_ids[bit] = id;
		visiting.insert(bit);
		BitNode node;
		for (auto select : s) node.sel.push_back(control(select));
		node.slots.push_back(add_cone(a[offset], depth + 1));
		for (int i = 0; i < GetSize(s); i++) node.slots.push_back(add_cone(b[i * width + offset], depth + 1));
		cone[id] = node;
		visiting.erase(bit);
		return id;
	}

	static bool value(int slot, const std::vector<bool> &values)
	{
		log_assert(slot != -3);
		return slot == -2 || (slot >= 0 && values[slot]);
	}

	bool resolve(int slot, const std::vector<bool> &values, SigBit &out)
	{
		if (slot < 0) { out = canonical_data(sources[-1 - slot]); return true; }
		const auto &node = cone[slot];
		bool selected = false;
		for (int i = 0; i < GetSize(node.sel); i++) if (value(node.sel[i], values)) {
			SigBit data;
			if (!resolve(node.slots[i + 1], values, data) || (selected && data != out)) return false;
			out = data;
			selected = true;
		}
		return selected || resolve(node.slots[0], values, out);
	}

	SigBit canonical_data(SigBit bit)
	{
		if (!reusable_signal(bit)) return bit;
		if (equivalent_q.count(bit)) bit = equivalent_q.at(bit);
		if (!data_aliases.count(bit) || !valid_index(data_aliases.at(bit))) return bit;
		SigBit target = data_aliases.at(bit).bit;
		if (!reusable_signal(target)) return bit;
		return equivalent_q.count(target) ? equivalent_q.at(target) : target;
	}

	bool evaluable(Cell *cell)
	{
		return cell->known() && StaticCellTypes::categories.is_evaluable(cell->type) && cell->hasPort(ID::Y) &&
			!protected_cells.count(cell) && !retired.count(cell) &&
			GetSize(cell_inputs[cell]) <= 256 && GetSize(cell_outputs[cell]) <= 256;
	}

	bool safe_signal(SigBit bit, pool<Cell *> &busy, int depth, int &visited)
	{
		if (!spend(1)) return false;
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (ambiguous.count(bit)) return false;
		if (boundary.safe_bits.count(bit)) return boundary.safe_bits.at(bit);
		if (!drivers.count(bit)) return true;
		Cell *cell = drivers.at(bit).first;
		if (state_cells.count(cell)) return true;
		if (boundary.safe_cells.count(cell)) return boundary.safe_cells.at(cell);
		int64_t input_limit = cell->type.in(ID($mux), ID($pmux)) ? int64_t(4096) * (limits.cells + 2) : 256;
		if (busy.count(cell) || depth >= limits.cells || visited >= limits.cells ||
			!cell->known() || !(StaticCellTypes::categories.is_evaluable(cell->type) ||
				StaticCellTypes::categories.is_combinatorial(cell->type)) ||
			GetSize(cell_inputs[cell]) > input_limit) return false;
		visited++;
		busy.insert(cell);
		bool safe = true;
		for (auto input : cell_inputs[cell]) if (!safe_signal(input, busy, depth + 1, visited)) { safe = false; break; }
		busy.erase(cell);
		if (GetSize(boundary.safe_cells) < limits.nodes) {
			boundary.safe_cells[cell] = safe;
			boundary.safe_cell_names[cell->name] = safe;
		}
		for (auto output : cell_outputs[cell])
			if (GetSize(boundary.safe_bits) < limits.nodes)
				boundary.safe_bits[output] = safe && !ambiguous.count(output);
		return safe;
	}

	bool supported_ff(const FfData &ff)
	{
		return ff.has_clk && !ff.has_gclk && !ff.has_aload && !ff.has_sr && !ff.is_fine && !ff.is_anyinit && ff.width <= 4096;
	}

	void build_boundaries()
	{
		for (auto cell : module->cells()) {
			if (exhausted) return;
			if (!state_cells.count(cell)) continue;
			FfData ff(&initvals, cell);
			bool safe = supported_ff(ff) && !protected_cells.count(cell);
			for (auto bit : sigmap(ff.sig_q))
				if (ambiguous.count(bit) || boundary.barriers.count(bit)) safe = false;
			pool<Cell *> busy;
			int visited = 0;
			for (auto bit : cell_inputs[cell])
				if (!safe_signal(bit, busy, 0, visited)) safe = false;
			boundary.safe_ffs[cell] = safe;
			boundary.safe_ff_names[cell->name] = safe;
		}
	}

	bool reference_safe(SigBit bit) const
	{
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (ambiguous.count(bit) || discarded_q.count(bit)) return false;
		if (!drivers.count(bit)) return true;
		Cell *owner = drivers.at(bit).first;
		IdString identity = original_names.at(owner);
		if (boundary.state_names.count(identity)) return true;
		return boundary.safe_cell_names.count(identity) && boundary.safe_cell_names.at(identity);
	}

	bool reusable_signal(SigBit bit) const
	{
		if (!reference_safe(bit) || boundary.barriers.count(bit)) return false;
		if (!drivers.count(bit)) return true;
		Cell *owner = drivers.at(bit).first;
		IdString identity = original_names.at(owner);
		if (boundary.protected_names.count(identity) || retired.count(owner)) return false;
		return !boundary.state_names.count(identity) || (boundary.safe_ff_names.count(identity) && boundary.safe_ff_names.at(identity));
	}

	bool collect_dependencies(SigBit bit, pool<SigBit> &bits, pool<Cell *> &cells)
	{
		if (!spend(1) || !reference_safe(bit)) return false;
		if (!bits.insert(bit).second || !drivers.count(bit)) return true;
		Cell *owner = drivers.at(bit).first;
		if (state_cells.count(owner) || !cells.insert(owner).second) return true;
		if (GetSize(cells) > limits.cells) return false;
		for (auto input : cell_inputs[owner]) if (!collect_dependencies(input, bits, cells)) return false;
		return true;
	}

	bool index_dependencies(Cell *cell)
	{
		if (boundary.dependencies.count(cell)) return true;
		pool<SigBit> bits;
		pool<Cell *> cells;
		for (auto bit : cell_inputs[cell]) if (!collect_dependencies(bit, bits, cells)) return false;
		if (GetSize(bits) > int64_t(limits.nodes) * 8 - boundary.items) { exhausted = true; return false; }
		boundary.items += GetSize(bits);
		boundary.dependencies[cell] = std::move(bits);
		return true;
	}

	bool valid_index(const IndexedSignal &entry) const
	{
		if (!entry.owner || !boundary.dependencies.count(entry.owner) ||
			entry.identity != original_names.at(entry.owner) || module->cell(entry.identity) != entry.owner ||
			retired.count(entry.owner) || !reusable_signal(entry.bit)) return false;
		for (auto bit : boundary.dependencies.at(entry.owner)) if (!reusable_signal(bit)) return false;
		return true;
	}

	// 检查 ConstEval 将访问的完整控制区域，限制递归、输入数和单元数。
	bool check_control(SigBit bit, const pool<SigBit> &leaves, pool<Cell *> &done, pool<Cell *> &busy, int depth)
	{
		if (!spend(1)) return false;
		if (!reference_safe(bit)) return false;
		if (!bit.wire || leaves.count(bit)) return true;
		if (boundary.barriers.count(bit)) return false;
		if (depth >= limits.cells || ambiguous.count(bit) || !drivers.count(bit)) return false;
		Cell *cell = drivers.at(bit).first;
		if (done.count(cell)) return true;
		if (busy.count(cell) || !evaluable(cell) || GetSize(done) + GetSize(busy) >= limits.cells) return false;
		busy.insert(cell);
		for (auto input : cell_inputs[cell]) if (!check_control(input, leaves, done, busy, depth + 1)) return false;
		// ConstEval 对整个输出端口赋值，叶子不能与该端口重叠。
		for (auto output : cell_outputs[cell]) if (leaves.count(output) || ambiguous.count(output)) return false;
		busy.erase(cell);
		done.insert(cell);
		return true;
	}

	SigSpec expanded_controls(const std::vector<SigBit> &initial, int leaf_limit)
	{
		pool<SigBit> front(initial.begin(), initial.end());
		pool<Cell *> tried, expanded;
		for (int step = 0; step < limits.cells; step++) {
			if (!spend(int64_t(GetSize(front) + 1) * (limits.cells + 1))) break;
			bool changed = false;
			std::vector<SigBit> ordered(front.begin(), front.end());
			std::sort(ordered.begin(), ordered.end());
			for (auto bit : ordered) {
				if (!front.count(bit) || !drivers.count(bit) || ambiguous.count(bit) || boundary.barriers.count(bit)) continue;
				Cell *cell = drivers.at(bit).first;
				if (tried.count(cell) || !evaluable(cell)) continue;
				if (!spend(GetSize(cell_inputs[cell]) + GetSize(cell_outputs[cell]) + GetSize(front))) break;
				tried.insert(cell);
				pool<SigBit> next = front;
				for (auto output : cell_outputs[cell]) next.erase(output);
				bool ok = true;
				for (auto input : cell_inputs[cell]) if (input.wire) {
					if (ambiguous.count(input) || (drivers.count(input) &&
						(drivers.at(input).first == cell || expanded.count(drivers.at(input).first)))) ok = false;
					next.insert(input);
				}
				if (ok && GetSize(next) <= leaf_limit) {
					front = next;
					expanded.insert(cell);
					changed = true;
				}
			}
			if (!changed) break;
		}
		std::vector<SigBit> result(front.begin(), front.end());
		std::sort(result.begin(), result.end());
		return SigSpec(result);
	}

	bool tabulate(const SigSpec &leaves, int root, const FfData &ff,
		std::vector<SigBit> &data, std::vector<bool> &enable, std::vector<bool> &reset)
	{
		int n = GetSize(leaves);
		if (n > limits.leaves || (int64_t(1) << n) > limits.rows) return false;
		pool<SigBit> leaf_set;
		for (auto bit : leaves) leaf_set.insert(bit);
		pool<Cell *> done, busy;
		for (auto bit : ctrl) if (!check_control(bit, leaf_set, done, busy, 0)) return false;
		int rows = 1 << n;
		int64_t weight = GetSize(cone) + GetSize(ctrl) + 1;
		for (auto &node : cone) weight += GetSize(node.slots) + GetSize(node.sel);
		for (auto cell : done) weight += GetSize(cell_inputs[cell]) + GetSize(cell_outputs[cell]);
		if (!spend(int64_t(rows) * weight)) return false;
		data.resize(rows); enable.resize(rows); reset.resize(rows);
		std::vector<bool> values(GetSize(ctrl));
		for (int p = 0; p < rows; p++) {
			ce.push();
			ce.set(leaves, Const(p, n));
			bool ok = true;
			for (int i = 0; i < GetSize(ctrl); i++) {
				SigSpec signal = ctrl[i];
				if (!ce.eval(signal) || !signal.is_fully_def()) { ok = false; break; }
				values[i] = signal.as_bool();
			}
			ce.pop();
			if (!ok) return false;
			enable[p] = !ff.has_ce || value(en_slot, values) == ff.pol_ce;
			reset[p] = ff.has_srst && value(reset_slot, values) == ff.pol_srst;
			if (!enable[p] || reset[p]) { data[p] = State::Sx; continue; }
			if (!resolve(root, values, data[p]) || (!data[p].wire && data[p] != State::S0 && data[p] != State::S1)) return false;
			if (ambiguous.count(data[p])) return false;
		}
		return true;
	}

	int mux_tree(const std::vector<int> &data, const std::vector<int> &select, int lo, int bit)
	{
		if (bit < 0) return data[lo];
		int mid = lo + (1 << bit);
		int a = mux_tree(data, select, lo, bit - 1);
		if (mid >= GetSize(data)) return a;
		return mux(a, mux_tree(data, select, mid, bit - 1), select[bit]);
	}

	bool encode(BitPlan &plan, const SigSpec &leaves, const std::vector<SigBit> &table,
		const std::vector<bool> &enable, const std::vector<bool> &reset, const FfData &ff, int offset, bool new_ce)
	{
		SigBit q = canonical_data(sigmap(ff.sig_q[offset]));
		if (!spend(int64_t(table.size()) * 4)) return false;
		std::vector<SigBit> data;
		pool<SigBit> data_seen;
		bool feedback = false;
		std::vector<TV> en(table.size(), TD);
		for (int p = 0; p < GetSize(table); p++) {
			bool update = table[p] != q;
			if (enable[p] && !reset[p]) {
				feedback |= !update;
				if ((!new_ce || update) && data_seen.insert(table[p]).second) data.push_back(table[p]);
			}
			// CE 优先时，复位有效域严格保持 E'=E；复位优先时该域允许无关项。
			bool active = enable[p] && ((ff.ce_over_srst && reset[p]) || update);
			if (!ff.ce_over_srst && reset[p]) en[p] = TD;
			else en[p] = active ? T1 : T0;
		}
		if (new_ce && !feedback) return false;
		plan.replace_ce = new_ce;
		plan.en = new_ce ? function(leaves, en) : -1;
		if (exhausted) return false;
		if (data.empty()) {
			State initial = ff.val_init[offset];
			data.push_back(initial == State::S0 || initial == State::S1 ? SigBit(initial) : q);
		}
		std::sort(data.begin(), data.end());
		int k = GetSize(data), bits = 0;
		while ((1 << bits) < k) bits++;
		// 同一数据函数直接连接原信号，常量与逐位恒等关系保持可见。
		if (k == 1) {
			plan.d = literal(data[0]);
			plan.shape = {0};
			return !exhausted;
		}
		std::vector<SigBit> order = data;
		int64_t best_cost = std::numeric_limits<int64_t>::max();
		int permutations = 0;
		do {
			if (!spend(int64_t(table.size()) * (bits + 2))) return false;
			dict<SigBit, int> codes;
			for (int i = 0; i < k; i++) codes[order[i]] = i;
			std::vector<int> select;
			for (int bit = 0; bit < bits; bit++) {
				std::vector<TV> truth(table.size(), TD);
				for (int p = 0; p < GetSize(table); p++) {
					if (!enable[p] || reset[p] || (new_ce && table[p] == q)) continue;
					int code = codes.at(table[p]);
					log_assert(code < k);
					int base = (code >> (bit + 1)) << (bit + 1);
					if (base + (1 << bit) < k) truth[p] = (code >> bit) & 1 ? T1 : T0;
				}
				int select_bit = function(leaves, truth);
				if (exhausted) return false;
				select.push_back(select_bit);
			}
			std::vector<int> inputs;
			for (auto source : order) {
				inputs.push_back(literal(source));
				if (exhausted) return false;
			}
			int d = mux_tree(inputs, select, 0, bits - 1);
			if (exhausted || d < 0 || (new_ce && plan.en < 0)) return false;
			pool<int> added;
			gather(d, added);
			if (new_ce) gather(plan.en, added);
			if (GetSize(added) < best_cost) {
				best_cost = GetSize(added);
				plan.d = d;
				plan.shape = select;
				plan.shape.insert(plan.shape.begin(), k);
			}
			permutations++;
		} while (k <= 5 && permutations < 24 && std::next_permutation(order.begin(), order.end()));
		return true;
	}

	// 原单元逐位成本：MUX、PMUX 与可枚举控制使用同一表达式生成器。
	void original_cost(Cell *cell, pool<int> &nodes)
	{
		if (cell->type.in(ID($mux), ID($pmux))) {
			SigSpec a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
			SigSpec y = sigmap(cell->getPort(ID::Y));
			int width = GetSize(a);
			if (GetSize(b) != width * GetSize(s) || GetSize(y) != width || s.empty()) return;
			std::vector<int> selectors;
			for (auto bit : s) {
				if (!bit.wire && bit != State::S0 && bit != State::S1) return;
				selectors.push_back(literal(bit));
			}
			int any = literal(State::S0);
			if (cell->type == ID($pmux)) for (int select : selectors) any = gate({any, select}, 0xe);
			for (int i = 0; i < width; i++) {
				if (!users[y[i]]) continue;
				if (!a[i].wire && a[i] != State::S0 && a[i] != State::S1) continue;
				if (cell->type == ID($mux)) {
					if (!b[i].wire && b[i] != State::S0 && b[i] != State::S1) continue;
					int root = mux(literal(canonical_data(a[i])), literal(canonical_data(b[i])), selectors[0]);
					if (exhausted) return;
					gather(root, nodes, nullptr, false);
					continue;
				}
				bool known = true;
				int combined = literal(State::S0);
				for (int j = 0; j < GetSize(s); j++) {
					SigBit bit = b[j * width + i];
					if (!bit.wire && bit != State::S0 && bit != State::S1) { known = false; break; }
					int term = gate({literal(canonical_data(bit)), selectors[j]}, 0x8);
					combined = gate({combined, term}, 0xe);
				}
				if (!known) continue;
				int root = mux(literal(canonical_data(a[i])), combined, any);
				if (exhausted) return;
				gather(root, nodes, nullptr, false);
			}
		} else if (evaluable(cell)) {
			pool<SigBit> inputs;
			for (auto bit : cell_inputs[cell]) if (bit.wire) inputs.insert(bit);
			for (auto bit : cell_outputs[cell]) if (inputs.count(bit) || ambiguous.count(bit)) return;
			if (GetSize(inputs) > limits.leaves || (int64_t(1) << GetSize(inputs)) > limits.rows) return;
			std::vector<SigBit> ordered(inputs.begin(), inputs.end());
			std::sort(ordered.begin(), ordered.end());
			SigSpec leaves(ordered), y = sigmap(cell->getPort(ID::Y));
			int rows = 1 << GetSize(leaves);
			if (!spend(int64_t(rows) * (GetSize(cell_inputs[cell]) + GetSize(y) + 1))) return;
			std::vector<std::vector<TV>> truth(GetSize(y), std::vector<TV>(rows, TD));
			for (int p = 0; p < rows; p++) {
				ce.push();
				ce.set(leaves, Const(p, GetSize(leaves)));
				SigSpec value = y;
				bool ok = ce.eval(value) && value.is_fully_def();
				ce.pop();
				if (!ok) return;
				for (int i = 0; i < GetSize(y); i++) truth[i][p] = value[i] == State::S1 ? T1 : T0;
			}
			for (int i = 0; i < GetSize(y); i++) if (users[y[i]]) {
				int root = function(leaves, truth[i]);
				if (exhausted) return;
				gather(root, nodes, nullptr, false);
			}
		}
	}

	bool droppable(Cell *cell)
	{
		if (cell->type.in(ID($mux), ID($pmux)) &&
			(GetSize(cell->getPort(ID::Y)) > 4096 || GetSize(cell->getPort(ID::S)) > limits.cells)) return false;
		if (!evaluable(cell) && !(cell->type.in(ID($mux), ID($pmux)) &&
			!protected_cells.count(cell) && !retired.count(cell) && GetSize(cell_outputs[cell]) <= 4096 &&
			GetSize(cell_inputs[cell]) <= int64_t(4096) * (limits.cells + 2))) return false;
		if (!boundary.safe_cells.count(cell) || !boundary.safe_cells.at(cell)) return false;
		for (auto bit : cell_outputs[cell]) if (ambiguous.count(bit) || boundary.barriers.count(bit)) return false;
		return true;
	}

	static std::pair<int, std::vector<int>> group_key(const BitPlan &bit)
	{
		return std::make_pair(bit.unused ? -3 : bit.constant ? -2 : bit.replace_ce ? bit.en : -1, bit.shape);
	}

	// settle() 与 apply() 共用：按 group_key 把位号分组。
	static std::map<std::pair<int, std::vector<int>>, std::vector<int>> group_bits(const FfData &ff, const std::vector<BitPlan> &bits)
	{
		std::map<std::pair<int, std::vector<int>>, std::vector<int>> groups;
		for (int i = 0; i < ff.width; i++) groups[group_key(bits[i])].push_back(i);
		return groups;
	}

	// 零收益只在确实化简了结构（有常量位或直连位）时放行，analyze() 与 analyze_group() 共用。
	static bool profitable(int64_t gain, bool useful)
	{
		return gain > 0 || (gain == 0 && useful);
	}

	bool constant_bit(const FfData &ff, int offset, int d)
	{
		if (!exprs[d].leaf || exprs[d].bit.wire) return false;
		State value = exprs[d].bit.data;
		return (value == State::S0 || value == State::S1) && ff.val_init[offset] == value &&
			(!ff.has_srst || ff.val_srst[offset] == value) && (!ff.has_arst || ff.val_arst[offset] == value);
	}

	MergeKey merge_key(const FfData &ff, int offset, SigBit d)
	{
		SigSpec signals = d;
		signals.append(ff.has_clk ? sigmap(ff.sig_clk) : SigSpec(State::S0));
		signals.append(ff.has_ce ? sigmap(ff.sig_ce) : SigSpec(State::S1));
		signals.append(ff.has_aload ? sigmap(ff.sig_aload) : SigSpec(State::S0));
		signals.append(ff.has_srst ? sigmap(ff.sig_srst) : SigSpec(State::S0));
		signals.append(ff.has_arst ? sigmap(ff.sig_arst) : SigSpec(State::S0));
		signals.append(ff.has_aload ? sigmap(ff.sig_ad[offset]) : SigBit(State::S0));
		signals.append(ff.has_sr ? sigmap(ff.sig_set[offset]) : SigBit(State::S0));
		signals.append(ff.has_sr ? sigmap(ff.sig_clr[offset]) : SigBit(State::S0));
		for (bool flag : {ff.has_clk, ff.has_gclk, ff.has_clk && ff.pol_clk, ff.has_ce,
			ff.has_ce && ff.pol_ce, ff.has_aload, ff.has_aload && ff.pol_aload, ff.has_srst,
			ff.has_srst && ff.pol_srst, ff.has_arst, ff.has_arst && ff.pol_arst, ff.has_sr,
			ff.has_sr && ff.pol_set, ff.has_sr && ff.pol_clr, ff.has_ce && ff.has_srst && ff.ce_over_srst,
			ff.is_fine, ff.has_gclk && ff.is_anyinit})
			signals.append(flag ? State::S1 : State::S0);
		signals.append(ff.val_init[offset]);
		signals.append(ff.has_srst ? ff.val_srst[offset] : State::Sx);
		signals.append(ff.has_arst ? ff.val_arst[offset] : State::Sx);
		std::vector<std::pair<IdString, Const>> attributes(ff.attributes.begin(), ff.attributes.end());
		std::sort(attributes.begin(), attributes.end());
		return std::make_pair(signals, attributes);
	}

	bool mergeable(const FfData &ff, int offset)
	{
		auto defined = [](State value) { return value == State::S0 || value == State::S1; };
		return defined(ff.val_init[offset]) && (!ff.has_srst || defined(ff.val_srst[offset])) &&
			(!ff.has_arst || defined(ff.val_arst[offset]));
	}

	int64_t attribute_size(const FfData &ff)
	{
		int64_t bytes = 0;
		for (auto &attribute : ff.attributes) bytes += 64 + (int64_t(GetSize(attribute.second)) + 7) / 8;
		return bytes;
	}

	void index_ff_relations()
	{
		std::map<MergeKey, std::vector<std::pair<Cell *, int>>> originals;
		for (auto cell : module->cells()) {
			if (exhausted) return;
			if (!boundary.safe_ffs.count(cell) || !boundary.safe_ffs.at(cell) || !index_dependencies(cell)) continue;
			FfData ff(&initvals, cell);
			int64_t bytes = attribute_size(ff);
			for (int i = 0; i < ff.width; i++) {
				SigBit q = sigmap(ff.sig_q[i]);
				if (!users[q] || !reusable_signal(q)) continue;
				if (!spend(1 + bytes)) return;
				if (GetSize(originals) >= limits.nodes) { exhausted = true; return; }
				if (bytes > int64_t(limits.nodes) * 64 - attribute_bytes) { exhausted = true; return; }
				auto key = merge_key(ff, i, sigmap(ff.sig_d[i]));
				key.second.erase(std::remove_if(key.second.begin(), key.second.end(),
					[](const std::pair<IdString, Const> &attribute) { return attribute.first == ID::src; }), key.second.end());
				if (!originals.count(key)) attribute_bytes += bytes;
				originals[key].emplace_back(cell, i);
			}
		}
		for (auto &entry : originals) {
			if (entry.second.size() < 2) continue;
			Cell *first = entry.second[0].first;
			FfData ff(&initvals, first);
			SigBit group = sigmap(ff.sig_q[entry.second[0].second]);
			bool proven = mergeable(ff, entry.second[0].second), selected = true;
			group_members.insert(group);
			for (auto member : entry.second) {
				FfData part(&initvals, member.first);
				SigBit q = sigmap(part.sig_q[member.second]);
				ff_groups[q] = group;
				if (proven) equivalent_q[q] = group;
				selected &= module->selected(member.first);
				ff_neighbors[first].insert(member.first);
				ff_neighbors[member.first].insert(first);
			}
			if (proven) state_groups.insert(group);
			if (!selected) {
				BitPlan unchanged;
				unchanged.d = literal(sigmap(ff.sig_d[entry.second[0].second]));
				unchanged.shape = {-1};
				if (exhausted) return;
				fixed_group_bits[group] = unchanged;
			}
		}
		log("OPT_RESHAPE_RELATIONS module=%s control_groups=%d state_groups=%d\n",
			log_id(module), GetSize(group_members), GetSize(state_groups));
	}

	void index_functions()
	{
		for (auto cell : module->cells()) {
			if (exhausted) return;
			if (!evaluable(cell)) continue;
			SigSpec y = sigmap(cell->getPort(ID::Y));
			bool safe = true;
			pool<Cell *> safety_busy;
			int visited = 0;
			for (auto bit : y) if (!safe_signal(bit, safety_busy, 0, visited) || !reusable_signal(bit)) safe = false;
			if (!safe || !index_dependencies(cell)) continue;
			for (auto bit : boundary.dependencies.at(cell)) if (!reusable_signal(bit)) safe = false;
			if (!safe) continue;
			for (auto bit : cell_inputs[cell]) if (ambiguous.count(bit) || (!bit.wire && bit != State::S0 && bit != State::S1)) safe = false;
			for (auto bit : y) if (ambiguous.count(bit) || !bit.wire) safe = false;
			if (!safe) continue;
			pool<SigBit> inputs;
			for (auto bit : cell_inputs[cell]) if (bit.wire) inputs.insert(bit);
			if (GetSize(inputs) > 4) continue;
			for (auto bit : y) if (inputs.count(bit)) safe = false;
			if (!safe) continue;
			std::vector<SigBit> outputs;
			for (auto bit : y) outputs.push_back(bit);
			SigSpec leaves = expanded_controls(outputs, 4);
			pool<SigBit> leaf_set;
			for (auto bit : leaves) leaf_set.insert(bit);
			pool<Cell *> done, busy;
			for (auto bit : y) if (!check_control(bit, leaf_set, done, busy, 0)) safe = false;
			if (!safe || GetSize(leaves) > 4) continue;
			int rows = 1 << GetSize(leaves);
			int64_t weight = 1;
			for (auto evaluated : done) weight += GetSize(cell_inputs[evaluated]) + GetSize(cell_outputs[evaluated]);
			if (!spend(int64_t(rows) * weight)) return;
			std::vector<unsigned> truth(GetSize(y), 0);
			for (int p = 0; p < rows; p++) {
				ce.push();
				ce.set(leaves, Const(p, GetSize(leaves)));
				SigSpec value = y;
				bool ok = ce.eval(value) && value.is_fully_def();
				ce.pop();
				if (!ok) { safe = false; break; }
				for (int i = 0; i < GetSize(y); i++) if (value[i] == State::S1) truth[i] |= 1u << p;
			}
			if (!safe) continue;
			std::vector<int> args;
			for (auto bit : leaves) args.push_back(literal(bit));
			for (int i = 0; i < GetSize(y); i++) {
				int id = gate(args, truth[i]);
				if (exhausted) return;
				if (!exprs[id].leaf && GetSize(existing_functions) < limits.nodes)
					existing_functions.insert(std::make_pair(id, IndexedSignal{cell, y[i], cell->name}));
				if (GetSize(data_aliases) < limits.nodes && reusable_signal(y[i])) {
					if (exprs[id].leaf && reusable_signal(exprs[id].bit))
						data_aliases[y[i]] = IndexedSignal{cell, exprs[id].bit, cell->name};
					else if (existing(id)) data_aliases[y[i]] = existing_functions.at(id);
				}
			}
		}
	}

	bool settle(Plan &plan, const FfData &ff)
	{
		log_assert(boundary.safe_ffs.at(plan.ff));
		plan.delta.clear(); plan.added.clear(); plan.dead.clear(); plan.removed = 0;
		for (auto bit : sigmap(ff.sig_d)) if (bit.wire) plan.delta[bit]--;
		for (int i = 0; i < ff.width; i++) if (!plan.bits[i].unused) gather(plan.bits[i].d, plan.added, &plan.delta);
		auto groups = group_bits(ff, plan.bits);
		for (auto &group : groups) {
			const auto &first = plan.bits[group.second[0]];
			if (first.replace_ce && !first.constant && !first.unused) gather(first.en, plan.added, &plan.delta);
		}
		if (ff.has_ce && sigmap(ff.sig_ce)[0].wire) {
			plan.delta[sigmap(ff.sig_ce)[0]]--;
			for (auto &group : groups) if (!plan.bits[group.second[0]].replace_ce &&
				!plan.bits[group.second[0]].constant && !plan.bits[group.second[0]].unused)
				plan.delta[sigmap(ff.sig_ce)[0]]++;
		}
		// 时钟和复位的连接出现次数与实际切分一致。
		int clocked_groups = 0;
		for (auto &group : groups) if (!plan.bits[group.second[0]].constant && !plan.bits[group.second[0]].unused) clocked_groups++;
		for (auto signal : {ff.sig_clk, ff.sig_srst, ff.sig_arst})
			for (auto bit : sigmap(signal)) if (bit.wire) plan.delta[bit] += clocked_groups - 1;
		std::vector<Cell *> queue;
		pool<int> original_nodes;
		for (auto &entry : plan.delta) if (drivers.count(entry.first)) queue.push_back(drivers.at(entry.first).first);
		for (size_t pos = 0; pos < queue.size(); pos++) {
			if (!spend(1)) return false;
			Cell *cell = queue[pos];
			if (plan.dead.count(cell) || !droppable(cell)) continue;
			if (!spend(GetSize(cell_inputs[cell]) + GetSize(cell_outputs[cell]))) return false;
			bool dead = true;
			for (auto bit : cell_outputs[cell]) {
				log_assert(users[bit] + plan.delta[bit] >= 0);
				if (users[bit] + plan.delta[bit]) dead = false;
			}
			if (!dead) continue;
			plan.dead.insert(cell);
			original_cost(cell, original_nodes);
			if (exhausted) return false;
			for (auto bit : cell_inputs[cell]) if (bit.wire) {
				plan.delta[bit]--;
				if (drivers.count(bit)) queue.push_back(drivers.at(bit).first);
			}
		}
		plan.cost = GetSize(plan.added);
		plan.removed = GetSize(original_nodes);
		return true;
	}

	bool bit_changed(const BitPlan &bit, SigBit original)
	{
		if (bit.constant || bit.unused || bit.replace_ce) return true;
		if (exprs[bit.d].leaf) return exprs[bit.d].bit != original;
		return !existing(bit.d) || existing_functions.at(bit.d).bit != original;
	}

	void remember_groups(const FfData &ff, const Plan *plan)
	{
		for (int i = 0; i < ff.width; i++) {
			SigBit q = sigmap(ff.sig_q[i]);
			if (!ff_groups.count(q) || fixed_group_bits.count(ff_groups.at(q))) continue;
			BitPlan bit;
			if (plan) bit = plan->bits[i];
			else {
				bit.d = leaf_ids.at(sigmap(ff.sig_d[i]));
				bit.shape = {-1};
			}
			fixed_group_bits[ff_groups.at(q)] = bit;
		}
	}

	void analyze(Cell *cell)
	{
		if (exhausted || !boundary.safe_ffs.count(cell) || !boundary.safe_ffs.at(cell) || !index_dependencies(cell)) return;
		FfData ff(&initvals, cell);
		if (ff.has_ce && literal(sigmap(ff.sig_ce)[0]) < 0) return;
		Plan keep, enable;
		keep.ff = enable.ff = cell;
		dict<SigBit, std::pair<BitPlan, BitPlan>> local_groups;
		bool changed = false;
		for (int offset = 0; offset < ff.width; offset++) {
			SigBit original = sigmap(ff.sig_d[offset]);
			BitPlan unchanged;
			unchanged.d = literal(original);
			unchanged.shape = {-1};
			if (exhausted) return;
			SigBit q = sigmap(ff.sig_q[offset]);
			bool grouped = ff_groups.count(q);
			SigBit group = grouped ? ff_groups.at(q) : q;
			if (grouped && (fixed_group_bits.count(group) || local_groups.count(group))) {
				BitPlan a = fixed_group_bits.count(group) ? fixed_group_bits.at(group) : local_groups.at(group).first;
				BitPlan b = fixed_group_bits.count(group) ? a : local_groups.at(group).second;
				keep.bits.push_back(a); enable.bits.push_back(b);
				changed |= bit_changed(a, original) || bit_changed(b, original);
				continue;
			}
			if (!users[q]) {
				unchanged.unused = true;
				unchanged.shape = {-3};
				keep.bits.push_back(unchanged);
				enable.bits.push_back(unchanged);
				changed = true;
				continue;
			}
			BitPlan best_keep = unchanged, best_enable = unchanged;
			bool have_enable = false;
			cone.clear(); cone_ids.clear(); visiting.clear(); sources.clear(); source_ids.clear(); ctrl.clear(); ctrl_ids.clear();
			cone_bad = false;
			int root = add_cone(original);
			en_slot = ff.has_ce ? control(sigmap(ff.sig_ce)[0]) : -2;
			reset_slot = ff.has_srst ? control(sigmap(ff.sig_srst)[0]) : -1;
			pool<Cell *> busy;
			int visited = 0;
			for (auto bit : ctrl) if (!safe_signal(bit, busy, 0, visited)) cone_bad = true;
			for (auto bit : sources) if (!safe_signal(bit, busy, 0, visited)) cone_bad = true;
			if (root >= 0 && !cone_bad && !exhausted) {
				std::vector<SigSpec> options;
				if (GetSize(ctrl) <= limits.leaves) {
					auto ordered = ctrl;
					std::sort(ordered.begin(), ordered.end());
					options.emplace_back(ordered);
				}
				SigSpec deep = expanded_controls(ctrl, limits.leaves);
				if ((options.empty() || deep != options[0]) && GetSize(deep) <= limits.leaves) options.push_back(deep);
				int64_t keep_cost = std::numeric_limits<int64_t>::max(), enable_cost = keep_cost;
				for (auto &leaves : options) {
					std::vector<SigBit> data;
					std::vector<bool> e, r;
					if (!tabulate(leaves, root, ff, data, e, r)) { unsafe++; continue; }
					for (int mode = 0; mode < 2; mode++) {
						if (mode && grouped && (!state_groups.count(group) || group_ce_mode == 0)) continue;
						BitPlan candidate;
						if (!encode(candidate, leaves, data, e, r, ff, offset, mode != 0)) continue;
						// 原 D 被多个寄存器使用时保持其公共数据/控制形式。
						if (!grouped && ff_data_users[original] > 1 && (candidate.replace_ce || !exprs[candidate.d].leaf)) continue;
						if (candidate.replace_ce && exprs[candidate.en].leaf &&
							((!ff.has_ce && exprs[candidate.en].bit == State::S1) ||
							(ff.has_ce && ff.pol_ce && exprs[candidate.en].bit == sigmap(ff.sig_ce)[0]))) {
							candidate.replace_ce = false;
							candidate.en = -1;
						}
						pool<int> nodes;
						gather(candidate.d, nodes);
						if (candidate.replace_ce) gather(candidate.en, nodes);
						if (!mode && GetSize(nodes) < keep_cost) { best_keep = candidate; keep_cost = GetSize(nodes); }
						if (mode && GetSize(nodes) < enable_cost) {
							best_enable = candidate; enable_cost = GetSize(nodes);
							have_enable = true;
						}
					}
				}
			}
			if (exhausted) return;
			if (!have_enable) best_enable = best_keep;
			if (original == canonical_data(sigmap(ff.sig_q[offset])) &&
				(ff.val_init[offset] == State::S0 || ff.val_init[offset] == State::S1)) {
				int initial = literal(ff.val_init[offset]);
				if (exhausted) return;
				if (constant_bit(ff, offset, initial)) {
					best_keep.d = best_enable.d = initial;
				}
			}
			best_keep.constant = constant_bit(ff, offset, best_keep.d);
			best_enable.constant = constant_bit(ff, offset, best_enable.d);
			if (best_keep.constant) { best_keep.replace_ce = false; best_keep.shape = {-2}; }
			if (best_enable.constant) { best_enable.replace_ce = false; best_enable.shape = {-2}; }
			if (grouped) local_groups[group] = std::make_pair(best_keep, best_enable);
			changed |= best_keep.d != unchanged.d || best_enable.d != unchanged.d || best_enable.replace_ce || best_keep.constant;
			keep.bits.push_back(best_keep);
			enable.bits.push_back(best_enable);
		}
		if (!changed) { remember_groups(ff, nullptr); return; }
		if (!settle(keep, ff) || !settle(enable, ff)) return;
		Plan constants;
		constants.ff = cell;
		constants.bits = keep.bits;
		bool any_constant = false;
		for (auto &bit : constants.bits) any_constant |= bit.constant || bit.unused;
		for (int i = 0; i < ff.width; i++) if (!constants.bits[i].constant && !constants.bits[i].unused) {
			SigBit q = sigmap(ff.sig_q[i]);
			if (ff_groups.count(q) && fixed_group_bits.count(ff_groups.at(q))) continue;
			constants.bits[i] = BitPlan();
			constants.bits[i].d = literal(sigmap(ff.sig_d[i]));
			constants.bits[i].shape = {-1};
		}
		if (any_constant && !settle(constants, ff)) return;
		Plan *chosen = enable.removed - enable.cost > keep.removed - keep.cost ? &enable : &keep;
		if (any_constant && constants.removed - constants.cost > chosen->removed - chosen->cost) chosen = &constants;
		if (prefer_enable) for (int i = 0; i < ff.width; i++) {
			SigBit q = sigmap(ff.sig_q[i]);
			if (ff_groups.count(q) && state_groups.count(ff_groups.at(q)) && enable.bits[i].replace_ce) {
				chosen = &enable; break;
			}
		}
		Plan &best = *chosen;
		int64_t gain = best.removed - best.cost;
		bool has_constant = false;
		bool has_direct = false;
		bool actual_change = false;
		for (int i = 0; i < ff.width; i++) {
			auto &bit = best.bits[i];
			has_constant |= bit.constant || bit.unused;
			has_direct |= exprs[bit.d].leaf && exprs[bit.d].bit != sigmap(ff.sig_d[i]);
			actual_change |= bit_changed(bit, sigmap(ff.sig_d[i]));
		}
		if (!actual_change) { remember_groups(ff, nullptr); return; }
		if (!force && !group_mode && !profitable(gain, has_constant || has_direct)) {
			rejected++; remember_groups(ff, nullptr); return;
		}
		int64_t items = best.bits.size() + best.delta.size() + best.dead.size() + best.added.size();
		for (auto &bit : best.bits) items += bit.shape.size();
		if (items > int64_t(limits.nodes) * 8 - saved_items) { exhausted = true; return; }
		saved_items += items;
		account_plan(best, ff, true);
		remember_groups(ff, &best);
		plans.push_back(best);
		accepted++;
	}

	void account_plan(const Plan &plan, const FfData &ff, bool retain)
	{
		for (const auto &entry : plan.delta)
			users[entry.first] += retain ? entry.second : -entry.second;
		for (auto dead : plan.dead) {
			if (retain) retired.insert(dead);
			else retired.erase(dead);
		}
		for (int i = 0; i < ff.width; i++) if (plan.bits[i].unused) {
			SigBit q = sigmap(ff.sig_q[i]);
			if (retain) discarded_q.insert(q);
			else discarded_q.erase(q);
		}
		for (int id : plan.added) {
			if (retain) committed.insert(id);
			else committed.erase(id);
		}
	}

	std::pair<int64_t, bool> component_score(size_t first)
	{
		int64_t gain = 0;
		bool useful = false;
		for (size_t p = first; p < plans.size(); p++) {
			gain += plans[p].removed - plans[p].cost;
			FfData ff(&initvals, plans[p].ff);
			for (int i = 0; i < ff.width; i++) {
				const auto &bit = plans[p].bits[i];
				useful |= bit.constant || bit.unused || (exprs[bit.d].leaf && exprs[bit.d].bit != sigmap(ff.sig_d[i]));
			}
		}
		return std::make_pair(gain, useful);
	}

	void undo_component(size_t first, int64_t old_items, const std::vector<Cell *> &component, const pool<SigBit> &original_fixed)
	{
		for (size_t p = plans.size(); p > first; p--) {
			auto &plan = plans[p - 1];
			FfData ff(&initvals, plan.ff);
			account_plan(plan, ff, false);
		}
		accepted -= int(plans.size() - first);
		plans.resize(first);
		saved_items = old_items;
		for (auto owner : component) for (auto q : sigmap(owner->getPort(ID::Q)))
			if (ff_groups.count(q) && !original_fixed.count(ff_groups.at(q))) fixed_group_bits.erase(ff_groups.at(q));
	}

	void analyze_group(Cell *cell)
	{
		if (analyzed.count(cell) || exhausted) return;
		std::vector<Cell *> component{cell};
		pool<Cell *> seen{cell};
		pool<SigBit> original_fixed;
		for (size_t i = 0; i < component.size(); i++)
			for (auto neighbor : ff_neighbors[component[i]])
				if (module->selected(neighbor) && seen.insert(neighbor).second) component.push_back(neighbor);
		std::sort(component.begin(), component.end(), [](Cell *a, Cell *b) { return a->name < b->name; });
		bool joint_enable = false;
		for (auto owner : component) {
			analyzed.insert(owner);
			for (auto q : sigmap(owner->getPort(ID::Q))) if (ff_groups.count(q)) {
				SigBit group = ff_groups.at(q);
				if (fixed_group_bits.count(group)) original_fixed.insert(group);
				else if (state_groups.count(group)) joint_enable = true;
			}
		}
		size_t first = plans.size();
		int64_t old_items = saved_items;
		group_mode = component.size() > 1 || joint_enable;
		group_ce_mode = joint_enable ? 0 : -1;
		for (auto owner : component) analyze(owner);
		auto score = component_score(first);
		if (!exhausted && joint_enable) {
			std::vector<Plan> original(plans.begin() + first, plans.end());
			int64_t first_items = saved_items;
			dict<SigBit, BitPlan> first_fixed;
			for (auto owner : component) for (auto q : sigmap(owner->getPort(ID::Q)))
				if (ff_groups.count(q) && !original_fixed.count(ff_groups.at(q)) && fixed_group_bits.count(ff_groups.at(q)))
					first_fixed[ff_groups.at(q)] = fixed_group_bits.at(ff_groups.at(q));
			undo_component(first, old_items, component, original_fixed);
			prefer_enable = true;
			group_ce_mode = 1;
			for (auto owner : component) analyze(owner);
			prefer_enable = false;
			auto trial = component_score(first);
			log("OPT_RESHAPE_GROUP module=%s first_ff=%s cells=%d preserve_gain=%lld enable_gain=%lld enable_useful=%d complete=%d\n",
				log_id(module), log_id(component[0]), GetSize(component), (long long)score.first,
				(long long)trial.first, int(trial.second), int(!exhausted));
			if (exhausted || trial.first < score.first || (trial.first == score.first && !trial.second)) {
				undo_component(first, old_items, component, original_fixed);
				for (auto &plan : original) {
					FfData ff(&initvals, plan.ff);
					account_plan(plan, ff, true);
					plans.push_back(std::move(plan)); accepted++;
				}
				for (auto &entry : first_fixed) fixed_group_bits[entry.first] = entry.second;
				saved_items = first_items;
			} else score = trial;
		} else if (exhausted) {
			undo_component(first, old_items, component, original_fixed);
			group_mode = false;
			group_ce_mode = -1;
			return;
		}
		group_mode = false;
		group_ce_mode = -1;
		if (!force && !profitable(score.first, score.second)) {
			undo_component(first, old_items, component, original_fixed);
			rejected++;
			return;
		}
		for (size_t p = first; p < plans.size(); p++)
			log("MUXLEDGER pass=opt_reshape module=%s decision=%s gain=%lld removed=%lld added=%lld bits=%d\n",
				log_id(module), force ? "forced" : "accept", (long long)(plans[p].removed - plans[p].cost),
				(long long)plans[p].removed, (long long)plans[p].cost, GetSize(plans[p].bits));
	}

	SigBit emit(int id)
	{
		if (exprs[id].leaf) return exprs[id].bit;
		if (existing(id)) return existing_functions.at(id).bit;
		if (emitted.count(id)) return emitted.at(id);
		SigSpec inputs;
		for (int a : exprs[id].args) inputs.append(emit(a));
		Const truth(State::S0, 1 << GetSize(inputs));
		for (int p = 0; p < GetSize(truth); p++) if ((exprs[id].table >> p) & 1) truth.set(p, State::S1);
		Wire *out = module->addWire(NEW_ID);
		module->addLut(NEW_ID, inputs, out, truth);
		emitted[id] = SigBit(out);
		return SigBit(out);
	}

	int expression_identity(int id)
	{
		if (existing(id) && leaf_ids.count(existing_functions.at(id).bit)) return leaf_ids.at(existing_functions.at(id).bit);
		return id;
	}

	FinalMergeKey final_merge_key(const FfData &ff, int offset, const BitPlan &bit)
	{
		FfData controls = ff;
		int en = -1;
		if (bit.replace_ce) {
			controls.has_ce = true;
			controls.pol_ce = true;
			en = expression_identity(bit.en);
		} else if (ff.has_ce) {
			SigBit signal = sigmap(ff.sig_ce)[0];
			if (!leaf_ids.count(signal)) return std::make_pair(MergeKey(), std::make_pair(-1, -1));
			en = leaf_ids.at(signal);
		}
		if (controls.has_ce) controls.sig_ce = State::S0;
		return std::make_pair(merge_key(controls, offset, State::S0), std::make_pair(expression_identity(bit.d), en));
	}

	void prepare_commit()
	{
		CellMap<const Plan *> by_cell;
		for (auto &plan : plans) {
			log_assert(boundary.safe_ffs.at(plan.ff));
			by_cell[plan.ff] = &plan;
		}
		// 代表只登记最终状态转移关系，原始关系由独立索引保存。
		ff_representatives.clear();
		attribute_bytes = 0;
		for (auto cell : module->cells()) {
			if (!boundary.safe_ffs.count(cell) || !boundary.safe_ffs.at(cell) || !boundary.dependencies.count(cell)) continue;
			FfData ff(&initvals, cell);
			int64_t bytes = attribute_size(ff);
			for (int i = 0; i < ff.width; i++) {
				SigBit q = sigmap(ff.sig_q[i]);
				if (!users[q] || !mergeable(ff, i) || !reusable_signal(q)) continue;
				BitPlan bit;
				if (by_cell.count(cell)) bit = by_cell.at(cell)->bits[i];
				else {
					SigBit d = sigmap(ff.sig_d[i]);
					if (!leaf_ids.count(d)) continue;
					bit.d = leaf_ids.at(d);
				}
				if (bit.constant || bit.unused) continue;
				auto key = final_merge_key(ff, i, bit);
				if (key.second.first < 0) continue;
				if (GetSize(ff_representatives) >= limits.nodes || bytes > int64_t(limits.nodes) * 64 - attribute_bytes) return;
				if (ff_representatives.emplace(key, IndexedSignal{cell, q, cell->name}).second) attribute_bytes += bytes;
			}
		}
	}

	void apply(const Plan &plan)
	{
		log_assert(boundary.safe_ffs.at(plan.ff));
		FfData ff(&initvals, plan.ff);
		auto groups = group_bits(ff, plan.bits);
		std::vector<FfData> slices;
		for (auto &group : groups) {
			if (plan.bits[group.second[0]].unused) {
				for (int i : group.second) module->connect(ff.sig_q[i], State::Sx);
				continue;
			}
			FfData part = ff.slice(group.second);
			part.sig_d = SigSpec();
			for (int i : group.second) part.sig_d.append(emit(plan.bits[i].d));
			const auto &first = plan.bits[group.second[0]];
			if (first.replace_ce) {
				part.has_ce = true;
				part.pol_ce = true;
				part.sig_ce = emit(first.en);
			}
			if (first.constant) {
				part.has_clk = part.has_ce = part.has_srst = part.has_arst = false;
			} else {
				std::vector<int> unique;
				for (int i = 0; i < part.width; i++) {
					if (!mergeable(part, i)) {
						unique.push_back(i); continue;
					}
					int offset = group.second[i];
					auto key = final_merge_key(ff, offset, plan.bits[offset]);
					auto found = ff_representatives.find(key);
					if (found != ff_representatives.end() && found->second.bit != sigmap(part.sig_q[i])) {
						log_assert(reusable_signal(found->second.bit) &&
							found->second.identity == original_names.at(drivers.at(found->second.bit).first));
						module->connect(part.sig_q[i], found->second.bit);
					} else unique.push_back(i);
				}
				if (GetSize(unique) != part.width) part = part.slice(unique);
			}
			if (part.width) slices.push_back(part);
		}
		int width = 0;
		for (auto &part : slices) width += part.width;
		log_assert(width <= ff.width);
		int retained = -1;
		for (int i = 0; i < GetSize(slices); i++) {
			const auto &part = slices[i];
			if (part.has_clk && part.has_ce == ff.has_ce &&
				(!ff.has_ce || (part.pol_ce == ff.pol_ce && sigmap(part.sig_ce) == sigmap(ff.sig_ce)))) {
				retained = i; break;
			}
		}
		if (retained < 0) ff.remove();
		else {
			const auto &part = slices[retained];
			ff.remove_init();
			plan.ff->setParam(ID::WIDTH, part.width);
			plan.ff->setPort(ID::D, part.sig_d);
			plan.ff->setPort(ID::Q, part.sig_q);
			if (part.has_srst) plan.ff->setParam(ID::SRST_VALUE, part.val_srst);
			if (part.has_arst) plan.ff->setParam(ID::ARST_VALUE, part.val_arst);
			initvals.set_init(part.sig_q, part.val_init);
		}
		for (int i = 0; i < GetSize(slices); i++) if (i != retained) slices[i].emit();
	}

	void commit()
	{
		if (plans.empty()) return;
		prepare_commit();
		for (auto &plan : plans) apply(plan);
		for (auto cell : retired) module->remove(cell);
	}
};

struct OptReshapePass : Pass {
	OptReshapePass() : Pass("opt_reshape", "restructure register next-state control logic") { }
	static int64_t number(const std::string &text, const std::string &option)
	{
		int64_t value;
		auto parsed = std::from_chars(text.data(), text.data() + text.size(), value);
		if (parsed.ec != std::errc() || parsed.ptr != text.data() + text.size())
			log_error("Invalid numeric value for %s.\n", option.c_str());
		return value;
	}
	void help() override
	{
		log("\n    opt_reshape [options] [selection]\n\n");
		log("Enumerate bounded register control cones and preserve per-bit identities,\n");
		log("constants, feedback, initialization and reset values. Compare the original\n");
		log("CE representation with a legal feedback-derived CE, including synchronous\n");
		log("reset priority. Equal control/data functions share LUT4 expressions across\n");
		log("the module. Register slices retain all FfData control fields and attributes.\n\n");
		log("    -max_leaves <n>   control inputs per bit, default 10, range 1..20\n");
		log("    -max_cells <n>    cone cells and recursion depth, default 64, range 1..256\n");
		log("    -max_rows <n>     truth-table rows, default 4096, range 2..65536\n");
		log("    -max_nodes <n>    module expression cache, default 131072, range 2..1048576\n");
		log("    -max_work <n>     module work units, default 40000000, range 1..1000000000\n");
		log("    -dry-run          analyze without modifying modules\n");
		log("    -force            apply legal plans regardless of estimated gain\n\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		Limits limits;
		bool dry = false, force = false;
		log_header(design, "Executing OPT_RESHAPE pass (per-bit register control restructuring).\n");
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-dry-run") { dry = true; continue; }
			if (args[argidx] == "-force") { force = true; continue; }
			int *target = nullptr, low = 1, high = 0;
			if (args[argidx] == "-max_leaves") { target = &limits.leaves; high = 20; }
			if (args[argidx] == "-max_cells") { target = &limits.cells; high = 256; }
			if (args[argidx] == "-max_rows") { target = &limits.rows; low = 2; high = 65536; }
			if (args[argidx] == "-max_nodes") { target = &limits.nodes; low = 2; high = 1048576; }
			if (args[argidx] == "-max_work") {
				if (++argidx >= args.size()) log_error("Missing -max_work value.\n");
				limits.work = number(args[argidx], "-max_work");
				if (limits.work < 1 || limits.work > 1000000000) log_error("Invalid -max_work value.\n");
				continue;
			}
			if (!target) break;
			std::string option = args[argidx];
			if (++argidx >= args.size()) log_error("Missing %s value.\n", option.c_str());
			int64_t value = number(args[argidx], option);
			if (value < low || value > high) log_error("Invalid %s value: expected %d..%d.\n", option.c_str(), low, high);
			*target = value;
		}
		extra_args(args, argidx, design);
		int total = 0;
		for (auto module : design->selected_modules()) {
			ReshapeWorker worker(module, limits, force && !dry);
			worker.index_ff_relations();
			worker.index_functions();
			for (auto cell : module->selected_cells())
				if (StaticCellTypes::categories.is_ff(cell->type)) worker.analyze_group(cell);
			if (!dry) worker.commit();
			log("OPT_RESHAPE module=%s planned=%d no_gain=%d unsafe=%d work=%lld nodes=%d exhausted=%d\n",
				log_id(module), worker.accepted, worker.rejected, worker.unsafe, (long long)worker.work,
				GetSize(worker.exprs), int(worker.exhausted));
			total += worker.accepted;
		}
		log("%s %d registers.\n", dry ? "Planned" : "Restructured", total);
	}
} OptReshapePass;

PRIVATE_NAMESPACE_END
