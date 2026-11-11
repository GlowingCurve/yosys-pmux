#include "passes/opt/pmux_lut_cost.h"
#include "passes/opt/pmux_netlist.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN
namespace PmuxLutCost {
namespace {

constexpr uint16_t and_table = 8, or_table = 14, xor_table = 6, xnor_table = 9, mux_table = 0xca;
constexpr uint16_t not_table = 1, identity_table = 2, implication_table = 13, total_care = 0xffff;

bool spend_work(int &work, int64_t amount = 1)
{
	log_assert(amount >= 0);
	if (work < amount) {
		work = -1;
		return false;
	}
	work -= amount;
	return true;
}

bool sequential(Cell *cell)
{
	return StaticCellTypes::categories.is_ff(cell->type);
}

enum class Shape { Generic, Opaque, Unary, Bitwise, Mux, Pmux, Compare, Reduce, Logic };
enum class Kind { Opaque, Gate, Pmux, Compare, Reduce, Logic };

struct Expression {
	Kind kind = Kind::Opaque;
	SigSpec inputs;
	uint16_t table = 0, care_table = total_care;
	int split = 0;
	bool invert = false;
};

struct TruthTable {
	SigSpec inputs;
	std::vector<std::pair<uint16_t, uint16_t>> outputs;
};

using Signature = std::tuple<Kind, uint16_t, uint16_t, int, bool, SigSpec>;

bool can_share(const Expression &expression)
{
	return expression.kind != Kind::Gate || (GetSize(expression.inputs) > 0 &&
		!(GetSize(expression.inputs) == 1 && expression.table == identity_table));
}

Signature signature(const Expression &expression)
{
	auto inputs = expression.inputs;
	if (expression.kind == Kind::Gate && GetSize(inputs) == 2 &&
	    (expression.table == and_table || expression.table == or_table || expression.table == xor_table || expression.table == xnor_table))
		inputs.sort();
	return {expression.kind, expression.table, expression.care_table, expression.split, expression.invert, std::move(inputs)};
}

using ReadKey = std::pair<SigBit, int>;
enum class ReadKind { Leaf, Opaque, Fixed, Expanded };

struct Read {
	Signal signal;
	ReadKind kind;
	bool affected;
};

} // namespace

struct ModuleCost::Model {
	PmuxNetlist &netlist;
	decltype(netlist.revision()) revision;
	unsigned configuration = 0;
	pool<SigBit> boundaries, preserved, live;
	bool indexed = false;
	dict<Cell *, Shape> shapes;
	dict<Cell *, TruthTable> truth_tables;
	dict<SigBit, Expression> expressions;
	dict<Signature, std::vector<SigBit>> operators;

	explicit Model(PmuxNetlist &netlist) : netlist(netlist), revision(netlist.revision()) {}

	void sync()
	{
		if (revision == netlist.revision()) return;
		revision = netlist.revision();
		indexed = false;
		shapes.clear();
		truth_tables.clear();
		expressions.clear();
		live.clear();
		operators.clear();
	}

	Shape shape(Cell *cell, int &work)
	{
		auto found = shapes.find(cell);
		if (found != shapes.end()) return found->second;
		if (!spend_work(work)) return Shape::Opaque;
		auto sized = [&](IdString port, IdString parameter) {
			return cell->hasPort(port) && cell->hasParam(parameter) && GetSize(netlist.port(cell, port)) == cell->getParam(parameter).as_int();
		};
		IdString type = cell->type;
		Shape result = Shape::Generic;
		if (type.in(ID($mux), ID($pmux))) {
			result = Shape::Opaque;
			if (sized(ID::Y, ID::WIDTH) && sized(ID::A, ID::WIDTH) && cell->hasPort(ID::B) && cell->hasPort(ID::S)) {
				int width = GetSize(netlist.port(cell, ID::Y)), branches = GetSize(netlist.port(cell, ID::S));
				if (type == ID($mux) && branches == 1 && GetSize(netlist.port(cell, ID::B)) == width) result = Shape::Mux;
				if (type == ID($pmux) && sized(ID::S, ID::S_WIDTH) && GetSize(netlist.port(cell, ID::B)) == int64_t(width)*branches)
					result = Shape::Pmux;
			}
		} else if (type == ID($buf)) {
			result = sized(ID::Y, ID::WIDTH) && sized(ID::A, ID::WIDTH) ? Shape::Unary : Shape::Opaque;
		} else {
			bool unary = type.in(ID($not), ID($pos));
			bool binary = type.in(ID($and), ID($or), ID($xor), ID($xnor));
			bool compare = type.in(ID($eq), ID($ne));
			bool reduce = type.in(ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor));
			bool logic = type.in(ID($logic_and), ID($logic_or));
			if (unary || binary || compare || reduce || logic) {
				bool valid_a = sized(ID::Y, ID::Y_WIDTH) && sized(ID::A, ID::A_WIDTH) && cell->hasParam(ID::A_SIGNED);
				bool valid_b = !(binary || compare || logic) || (sized(ID::B, ID::B_WIDTH) && cell->hasParam(ID::B_SIGNED));
				result = !valid_a || !valid_b ? Shape::Opaque : unary ? Shape::Unary : binary ? Shape::Bitwise :
					compare ? Shape::Compare : reduce ? Shape::Reduce : Shape::Logic;
			}
		}
		return shapes[cell] = result;
	}

	TruthTable generic_truth(Cell *cell, int &work)
	{
		TruthTable result;
		if (!netlist.cell_evaluable(cell->type) || !cell->hasPort(ID::Y)) return result;
		bool mux = cell->type.in(ID($_MUX_), ID($_NMUX_), ID($bwmux));
		bool compound3 = cell->type.in(ID($_AOI3_), ID($_OAI3_));
		bool compound4 = cell->type.in(ID($_AOI4_), ID($_OAI4_));
		std::array<IdString, 4> port_names = {ID::A, ID::B, mux ? ID::S : ID::C, ID::D};
		int arguments = compound4 ? 4 : mux || compound3 ? 3 : 2;
		int size = 0;
		pool<SigBit> inputs;
		for (const auto &connection : cell->connections()) {
			const auto &signal = netlist.port(cell, connection.first);
			size += GetSize(signal);
			if (size > 64 || !spend_work(work)) return {};
			if (connection.first == ID::Y) continue;
			if (std::find(port_names.begin(), port_names.begin()+arguments, connection.first) == port_names.begin()+arguments) return {};
			for (auto bit : signal) {
				if (!spend_work(work)) return {};
				if (bit.wire) inputs.insert(bit);
				else if (bit != State::S0 && bit != State::S1) return {};
				if (GetSize(inputs) > 4) return {};
			}
		}
		if (cell->type == ID($lut) && GetSize(netlist.port(cell, ID::A)) > 8) return {};
		result.inputs = SigSpec(std::vector<SigBit>(inputs.begin(), inputs.end()));
		result.inputs.sort();
		dict<SigBit, int> positions;
		for (int i = 0; i < GetSize(result.inputs); i++) positions[result.inputs[i]] = i;
		int outputs = GetSize(netlist.port(cell, ID::Y));
		result.outputs.resize(outputs);
		int rows = 1 << GetSize(result.inputs);
		for (int row = 0; row < rows; row++) {
			if (!spend_work(work, size+1)) return {};
			std::array<Const, 4> args;
			for (int i = 0; i < arguments; i++) if (cell->hasPort(port_names[i]))
				for (auto bit : netlist.port(cell, port_names[i])) {
					State value = bit.wire ? (row & (1 << positions.at(bit)) ? State::S1 : State::S0) : bit.data;
					args[i].append(Const(value, 1));
				}
			bool error = false;
			Const values;
			if (arguments == 4) values = CellTypes::eval(cell, args[0], args[1], args[2], args[3], &error);
			else if (arguments == 3) values = CellTypes::eval(cell, args[0], args[1], args[2], &error);
			else values = CellTypes::eval(cell, args[0], args[1], &error);
			if (error || GetSize(values) != outputs) return {};
			for (int i = 0; i < outputs; i++) {
				if (values[i] == State::S1) result.outputs[i].first |= 1 << row;
				if (values[i] == State::S0 || values[i] == State::S1) result.outputs[i].second |= 1 << row;
			}
		}
		for (auto &output : result.outputs) if (output.second == (1u << rows)-1) output.second = total_care;
		return result;
	}

	Expression expression(SigBit bit, int &work)
	{
		if (!spend_work(work)) return {};
		auto found = expressions.find(bit);
		if (found != expressions.end()) return found->second;
		const auto *source = netlist.source(bit);
		log_assert(source && source->cell);
		auto cell = source->cell;
		int offset = source->offset;
		Expression result;
		if (source->port != ID::Y || sequential(cell)) return expressions[bit] = result;
		const auto &output = netlist.port(cell, ID::Y);
		log_assert(offset >= 0 && offset < GetSize(output) && output[offset] == bit);
		Shape form = shape(cell, work);
		IdString type = cell->type;
		if (form == Shape::Unary || form == Shape::Bitwise || form == Shape::Mux) {
			if (!spend_work(work, 3)) return {};
			result.kind = Kind::Gate;
			result.inputs.append(netlist.operand(cell, ID::A, offset));
			if (form != Shape::Unary) result.inputs.append(netlist.operand(cell, ID::B, offset));
			if (form == Shape::Mux) result.inputs.append(netlist.port(cell, ID::S));
			result.table = form == Shape::Mux ? mux_table : type == ID($not) ? not_table : form == Shape::Unary ? identity_table :
				type == ID($and) ? and_table : type == ID($or) ? or_table : type == ID($xor) ? xor_table : xnor_table;
		} else if (form == Shape::Pmux) {
			const auto &controls = netlist.port(cell, ID::S), &data = netlist.port(cell, ID::B);
			int branches = GetSize(controls);
			if (!spend_work(work, 1+2LL*branches)) return {};
			result.kind = Kind::Pmux;
			result.inputs.append(netlist.port(cell, ID::A)[offset]);
			result.inputs.append(controls);
			for (int i = 0; i < branches; i++) result.inputs.append(data[i*GetSize(output)+offset]);
			result.split = branches;
		} else if ((form == Shape::Compare || form == Shape::Reduce || form == Shape::Logic) && offset != 0) {
			result.kind = Kind::Gate;
		} else if (form == Shape::Compare) {
			result.kind = Kind::Compare;
			int width = std::max(GetSize(netlist.port(cell, ID::A)), GetSize(netlist.port(cell, ID::B)));
			if (!spend_work(work, 2LL*width)) return {};
		auto a = netlist.extended(cell, ID::A, width), b = netlist.extended(cell, ID::B, width);
			for (int i = 0; i < width; i++) {
			result.inputs.append(a[i]);
			result.inputs.append(b[i]);
			}
			result.invert = type == ID($ne);
		} else if (form == Shape::Reduce || form == Shape::Logic) {
			result.kind = form == Shape::Reduce ? Kind::Reduce : Kind::Logic;
			const auto &a = netlist.port(cell, ID::A);
			int64_t width = GetSize(a);
			if (form == Shape::Logic) width += GetSize(netlist.port(cell, ID::B));
			if (!spend_work(work, width)) return {};
			result.inputs = a;
			result.split = GetSize(a);
			if (form == Shape::Logic) result.inputs.append(netlist.port(cell, ID::B));
			result.table = type.in(ID($reduce_and), ID($logic_and)) ? and_table :
				type.in(ID($reduce_xor), ID($reduce_xnor)) ? xor_table : or_table;
			result.invert = type.in(ID($logic_not), ID($reduce_xnor));
		} else if (form == Shape::Generic) {
			auto truth = truth_tables.find(cell);
			if (truth == truth_tables.end()) {
				auto calculated = generic_truth(cell, work);
				if (work < 0) return {};
				truth = truth_tables.emplace(cell, std::move(calculated)).first;
			}
			if (!truth->second.outputs.empty()) {
				result.kind = Kind::Gate;
				result.inputs = truth->second.inputs;
				std::tie(result.table, result.care_table) = truth->second.outputs[offset];
			}
		}
		if (work < 0) return {};
		return expressions[bit] = std::move(result);
	}

	bool fixed(SigBit bit, Cell *cell) const
	{
		return netlist.kept(bit) || !netlist.selected(cell) || cell->get_bool_attribute(ID::keep);
	}

	bool index(int &work)
	{
		if (indexed) return work >= 0;
		const auto &protected_bits = netlist.protected_bits();
		if (!spend_work(work, int64_t(GetSize(protected_bits))+GetSize(preserved))) return false;
		std::vector<SigBit> pending(protected_bits.begin(), protected_bits.end());
		pending.insert(pending.end(), preserved.begin(), preserved.end());
		for (auto cell : netlist.module()->cells()) {
			if (!spend_work(work)) return false;
			if (netlist.selected(cell) && !cell->get_bool_attribute(ID::keep) && !netlist.uncertain_cell(cell) &&
			    (netlist.cell_evaluable(cell->type) || sequential(cell))) continue;
			for (const auto &connection : cell->connections()) {
				const auto &signal = netlist.port(cell, connection.first);
				if (!spend_work(work, GetSize(signal))) return false;
				for (auto bit : signal) pending.push_back(bit);
			}
		}
		pool<SigBit> active;
		pool<Cell *> opaque_cells;
		dict<Signature, std::vector<SigBit>> shared;
		for (int i = 0; i < GetSize(pending); i++) {
			if (!spend_work(work)) return false;
			auto bit = pending[i];
			if (!bit.wire || !active.insert(bit).second || boundaries.count(bit)) continue;
			const auto *source = netlist.source(bit);
			if (!source || !source->cell) continue;
			auto cell = source->cell;
			auto expr = expression(bit, work);
			if (work < 0) return false;
			if (expr.kind != Kind::Opaque) {
				if (!spend_work(work, GetSize(expr.inputs))) return false;
				for (auto input : expr.inputs) pending.push_back(input);
			if (can_share(expr) && !fixed(bit, cell)) shared[signature(expr)].push_back(bit);
			} else if (opaque_cells.insert(cell).second) {
				for (const auto &connection : cell->connections()) {
					if (netlist.cell_port_dir(cell->type, connection.first) == RTLIL::PD_OUTPUT) continue;
					const auto &signal = netlist.port(cell, connection.first);
					if (!spend_work(work, GetSize(signal))) return false;
					for (auto input : signal) pending.push_back(input);
				}
			}
		}
		live = std::move(active);
		operators = std::move(shared);
		indexed = true;
		return true;
	}

	bool observed(SigBit bit, const pool<SigBit> &modeled, const pool<SigBit> &excluded, int &work)
	{
		if (!live.count(bit)) return false;
		if (netlist.protected_bit(bit) || preserved.count(bit)) return true;
		for (const auto &use : netlist.users(bit)) {
			if (!spend_work(work)) return false;
			auto cell = use.cell;
			auto direction = netlist.cell_port_dir(cell->type, use.port);
			if (direction == RTLIL::PD_UNKNOWN || direction == RTLIL::PD_INOUT || !netlist.selected(cell) ||
			    cell->get_bool_attribute(ID::keep) || (!netlist.cell_evaluable(cell->type) && !sequential(cell))) return true;
			auto observed_output = [&](SigBit output) {
				return live.count(output) && !modeled.count(output) && !excluded.count(output) && !boundaries.count(output);
			};
			Shape form = shape(cell, work);
			if (work < 0) return false;
			if ((form == Shape::Unary || form == Shape::Bitwise || form == Shape::Mux || form == Shape::Pmux) && use.port != ID::S) {
				log_assert(use.port.in(ID::A, ID::B));
				const auto &output = netlist.port(cell, ID::Y);
				if (output.empty()) continue;
				int offset = form == Shape::Pmux && use.port == ID::B ? use.offset % GetSize(output) : use.offset;
				if (offset < GetSize(output) && observed_output(output[offset])) return true;
				if (form == Shape::Unary || form == Shape::Bitwise) {
					const auto &input = netlist.port(cell, use.port);
					if (use.offset == GetSize(input)-1 && GetSize(input) < GetSize(output) &&
					    netlist.operand(cell, use.port, GetSize(input)) == bit) {
						for (int i = GetSize(input); i < GetSize(output); i++) {
							if (!spend_work(work)) return false;
							if (observed_output(output[i])) return true;
						}
					}
				}
			} else if (form == Shape::Compare || form == Shape::Reduce || form == Shape::Logic) {
				const auto &output = netlist.port(cell, ID::Y);
				if (!output.empty() && observed_output(output[0])) return true;
			} else {
				for (const auto &connection : cell->connections()) {
					if (netlist.cell_port_dir(cell->type, connection.first) == RTLIL::PD_INPUT) continue;
					for (auto output : netlist.port(cell, connection.first)) {
						if (!spend_work(work)) return false;
						if (observed_output(output)) return true;
					}
				}
			}
		}
		return false;
	}

	bool prepare(const Request &request, int &work, std::vector<SigBit> &roots, pool<SigBit> &targets)
	{
		log_assert(!request.replacements.empty());
		sync();
		if (!spend_work(work, int64_t(GetSize(request.replacements))+GetSize(request.removed)+GetSize(request.roots)+GetSize(preserved))) return false;
		pool<SigBit> requested(preserved);
		for (const auto &entry : request.replacements) {
			auto bit = entry.first;
			log_assert(bit.wire && netlist.sigmap()(bit) == bit && entry.second && !boundaries.count(bit) && !request.removed.count(bit));
			requested.insert(bit);
			targets.insert(bit);
		}
		for (auto bit : request.roots) {
			bit = netlist.sigmap()(bit);
			if (bit.wire) requested.insert(bit);
		}
		for (auto bit : request.removed)
			log_assert(bit.wire && netlist.sigmap()(bit) == bit && !requested.count(bit) && !boundaries.count(bit));
		roots.assign(requested.begin(), requested.end());
		std::sort(roots.begin(), roots.end());
		return index(work);
	}
};

struct Snapshot::State {
	const ModuleCost *owner;
	std::size_t revision;
	unsigned configuration;
	std::vector<SigBit> roots, expanded;
	pool<SigBit> targets, removed, fixed;
	dict<ReadKey, Read> reads;
	LutCostGraph::ReadOnlyGraph topology;
	mutable LutCostGraph::CertificateCache certificates;
};

struct Builder::State {
	ModuleCost::Model &module;
	LutCostGraph &graph;
	const Request &request;
	bool changed;
	CostStatus status = CostStatus::NoGain;
	const Snapshot::State *snapshot = nullptr;
	bool checkpointing = false;
	dict<ReadKey, Read> reads;
	pool<SigBit> active, expanded;
	std::vector<SigBit> expanded_order;

	State(ModuleCost::Model &module, LutCostGraph &graph, const Request &request, bool changed) :
		module(module), graph(graph), request(request), changed(changed) {}

	void expand(SigBit bit)
	{
		if (expanded.insert(bit).second) expanded_order.push_back(bit);
	}

	void check_signal(Signal signal) const
	{
		int nodes = graph.node_count();
		log_assert(signal.value >= 0 && signal.value < nodes && signal.care >= 0 && signal.care < nodes);
	}

	int all_care(const std::vector<Signal> &args)
	{
		std::vector<int> care;
		for (auto arg : args) {
			if (arg.care == 0) return 0;
			if (arg.care != 1) care.push_back(arg.care);
		}
		return graph.reduce(and_table, std::move(care), 1);
	}

	Signal evaluate(Builder &builder, const Expression &expr, const std::vector<Signal> &args)
	{
		if (!graph.valid) return {0, 0};
		if (expr.kind == Kind::Pmux) {
			log_assert(GetSize(args) == 1+2*expr.split);
			return builder.pmux(args.front(), {args.begin()+1+expr.split, args.end()}, {args.begin()+1, args.begin()+1+expr.split});
		}
		if (expr.kind == Kind::Gate && expr.care_table == total_care) return builder.operation(expr.table, args);
		std::vector<int> values;
		for (auto arg : args) values.push_back(arg.value);
		int value;
		int care = all_care(args);
		switch (expr.kind) {
		case Kind::Gate:
			value = graph.gate(expr.table, values);
			if (care) {
				int defined = graph.gate(expr.care_table, values);
				care = care == 1 ? defined : graph.gate(and_table, {care, defined});
			}
			break;
		case Kind::Compare: {
			std::vector<int> terms;
			for (int i = 0; i < GetSize(values); i += 2) terms.push_back(graph.gate(xnor_table, {values[i], values[i+1]}));
			value = graph.reduce(and_table, std::move(terms), 1);
			break;
		}
		case Kind::Reduce:
			value = graph.reduce(expr.table, std::move(values), expr.table == and_table);
			break;
		case Kind::Logic: {
			int a = graph.reduce(or_table, {values.begin(), values.begin()+expr.split}, 0);
			int b = graph.reduce(or_table, {values.begin()+expr.split, values.end()}, 0);
			value = graph.gate(expr.table, {a, b});
			break;
		}
		default:
			log_abort();
			return {0, 0};
		}
		return {expr.invert ? graph.gate(not_table, {value}) : value, care};
	}
};

const char *status_name(CostStatus status)
{
	switch (status) {
	case CostStatus::Profitable: return "profitable";
	case CostStatus::NoGain: return "no-gain";
	case CostStatus::UnsupportedSource: return "unsupported-source";
	case CostStatus::UnsupportedActivatedBoundary: return "unsupported-activated-boundary";
	case CostStatus::DepthLimit: return "depth-limit";
	case CostStatus::NodeLimit: return "node-limit";
	case CostStatus::BudgetExhausted: return "budget-exhausted";
	}
	log_abort();
}

bool Builder::spend(int amount)
{
	log_assert(amount >= 0);
	return state.graph.spend(amount);
}

Signal Builder::fail(CostStatus reason)
{
	log_assert(reason != CostStatus::Profitable && reason != CostStatus::NoGain);
	if (state.graph.valid) state.status = reason;
	state.graph.valid = false;
	return {0, 0};
}

Signal Builder::operation(uint16_t table, const std::vector<Signal> &args)
{
	auto &graph = state.graph;
	if (!graph.valid) return {0, 0};
	std::vector<int> values;
	for (auto arg : args) {
		state.check_signal(arg);
		values.push_back(arg.value);
	}
	int value = graph.gate(table, values);
	if (table == mux_table && GetSize(args) == 3) {
		if (args[0].value == args[1].value && args[0].care == args[1].care) return {value, args[0].care};
		int selected_care = args[0].care == args[1].care ? args[0].care : graph.gate(mux_table, {args[0].care, args[1].care, args[2].value});
		int care = args[2].care == 1 ? selected_care : graph.gate(and_table, {args[2].care, selected_care});
		return {value, care};
	}
	return {value, state.all_care(args)};
}

Signal Builder::pmux(Signal fallback, const std::vector<Signal> &data, const std::vector<Signal> &controls)
{
	log_assert(GetSize(data) == GetSize(controls));
	auto &graph = state.graph;
	if (!graph.valid) return {0, 0};
	state.check_signal(fallback);
	int enabled = 0, collision = 0;
	std::vector<int> terms, qualification;
	for (int i = 0; i < GetSize(controls); i++) {
		auto control = controls[i];
		state.check_signal(control);
		state.check_signal(data[i]);
		terms.push_back(graph.gate(and_table, {data[i].value, control.value}));
		if (control.care != 1) qualification.push_back(control.care);
		if (data[i].care != 1) qualification.push_back(graph.gate(implication_table, {control.value, data[i].care}));
		if (enabled != 0 && control.value != 0)
			collision = graph.gate(or_table, {collision, graph.gate(and_table, {enabled, control.value})});
		enabled = graph.gate(or_table, {enabled, control.value});
	}
	int selected = graph.reduce(or_table, std::move(terms), 0);
	int value = fallback.value == 0 ? selected : graph.gate(mux_table, {fallback.value, selected, enabled});
	if (collision != 0) qualification.push_back(graph.gate(not_table, {collision}));
	if (fallback.care != 1) qualification.push_back(graph.gate(or_table, {enabled, fallback.care}));
	return {value, graph.reduce(and_table, std::move(qualification), 1)};
}

Signal Builder::bit(SigBit bit, int depth)
{
	if (!spend()) return {0, 0};
	if (depth <= 0) return fail(CostStatus::DepthLimit);
	bit = state.module.netlist.sigmap()(bit);
	if (!bit.wire) {
		log_assert(bit == RTLIL::S0 || bit == RTLIL::S1 || bit == RTLIL::Sx || bit == RTLIL::Sz);
		// 与 SatGen 一致，将高阻态导入为已定义的零。
		return {bit == RTLIL::S1, bit != RTLIL::Sx};
	}
	const auto &request = state.request;
	if (state.changed && request.removed.count(bit)) return fail(CostStatus::UnsupportedSource);
	ReadKey key = {bit, depth};
	auto found = state.reads.find(key);
	if (found != state.reads.end()) return found->second.signal;
	auto &graph = state.graph;
	if (state.snapshot) {
		auto saved = state.snapshot->reads.find(key);
		if (saved != state.snapshot->reads.end() && (!state.changed || !saved->second.affected)) {
			if (!state.changed) return saved->second.signal;
			const auto &read = saved->second;
			if (read.kind == ReadKind::Opaque && !state.module.live.count(bit)) return fail(CostStatus::UnsupportedActivatedBoundary);
			if (read.kind == ReadKind::Fixed) graph.add_fixed(bit);
			if (read.kind == ReadKind::Expanded) {
				state.expand(bit);
				const auto &expr = state.module.expressions.at(bit);
				for (auto input : expr.inputs) {
					this->bit(input, depth-1);
					if (!graph.valid) return {0, 0};
				}
			}
			state.reads[key] = read;
			return read.signal;
		}
	}
	if (!state.active.insert(bit).second) return fail(CostStatus::UnsupportedSource);
	Read read = {{0, 0}, ReadKind::Leaf, request.replacements.count(bit) || request.removed.count(bit)};
	auto replacement = request.replacements.find(bit);
	auto &netlist = state.module.netlist;
	const auto *source = netlist.source(bit);
	if (state.changed && replacement != request.replacements.end()) {
		read.signal = replacement->second(*this, depth-1);
	} else if (state.module.boundaries.count(bit)) {
		read.signal = {graph.leaf(bit), 1};
	} else if (netlist.uncertain(bit)) {
		read.signal = fail(CostStatus::UnsupportedSource);
	} else if (!source || !source->cell || sequential(source->cell)) {
		read.signal = {graph.leaf(bit), 1};
	} else {
		auto expr = state.module.expression(bit, graph.work);
		if (graph.work < 0) read.signal = fail(CostStatus::BudgetExhausted);
		else if (expr.kind == Kind::Opaque) {
			read.kind = ReadKind::Opaque;
			read.signal = state.changed && !state.module.live.count(bit) ? fail(CostStatus::UnsupportedActivatedBoundary) : Signal{graph.leaf(bit), 1};
		} else if (state.module.fixed(bit, source->cell)) {
			read.kind = ReadKind::Fixed;
			graph.add_fixed(bit);
			read.signal = {graph.leaf(bit), 1};
		} else {
			read.kind = ReadKind::Expanded;
			state.expand(bit);
			std::vector<Signal> args;
			for (auto input : expr.inputs) {
				args.push_back(this->bit(input, depth-1));
				if (!graph.valid) break;
				if (state.checkpointing && input.wire) read.affected |= state.reads.at({input, depth-1}).affected;
			}
			read.signal = state.evaluate(*this, expr, args);
		}
	}
	state.active.erase(bit);
	if (graph.valid) {
		state.check_signal(read.signal);
		state.reads[key] = read;
	}
	return read.signal;
}

Snapshot::Snapshot() = default;
Snapshot::~Snapshot() = default;

ModuleCost::ModuleCost(PmuxNetlist &netlist) : model(std::make_unique<Model>(netlist)) {}
ModuleCost::~ModuleCost() = default;

void ModuleCost::preserve(const SigSpec &boundary_outputs, const pool<SigBit> &roots)
{
	for (auto bit : boundary_outputs) {
		log_assert(bit.wire && model->netlist.sigmap()(bit) == bit);
		model->boundaries.insert(bit);
	}
	for (auto bit : roots) if (bit.wire) {
		log_assert(model->netlist.sigmap()(bit) == bit);
		model->preserved.insert(bit);
	}
	model->indexed = false;
	model->configuration++;
}

bool ModuleCost::modeled_inputs(SigBit bit, SigSpec &inputs, int &work)
{
	model->sync();
	bit = model->netlist.sigmap()(bit);
	const auto *source = model->netlist.source(bit);
	inputs = {};
	if (!source || !source->cell || model->boundaries.count(bit)) return false;
	auto expression = model->expression(bit, work);
	inputs = std::move(expression.inputs);
	return expression.kind != Kind::Opaque;
}

bool ModuleCost::observed_outside(SigBit bit, const pool<SigBit> &modeled, const pool<SigBit> &replaced, int &work)
{
	model->sync();
	bit = model->netlist.sigmap()(bit);
	return model->index(work) && model->observed(bit, modeled, replaced, work);
}

namespace {

CostStatus failure(int work, CostStatus before, CostStatus after = CostStatus::NoGain)
{
	if (work < 0) return CostStatus::BudgetExhausted;
	if (before != CostStatus::NoGain) return before;
	if (after != CostStatus::NoGain) return after;
	return CostStatus::NodeLimit;
}

} // namespace

CostStatus ModuleCost::checkpoint(const Request &request, int &work, Snapshot &snapshot)
{
	log_assert(!snapshot.state);
	auto saved = std::make_unique<Snapshot::State>();
	if (!model->prepare(request, work, saved->roots, saved->targets)) return CostStatus::BudgetExhausted;
	LutCostGraph graph(work);
	Builder::State state(*model, graph, request, false);
	state.checkpointing = true;
	Builder before(state);
	for (auto bit : saved->roots) {
		before.bit(bit);
		if (!graph.valid) return failure(work, state.status);
	}
	if (!spend_work(work, graph.node_count())) return CostStatus::BudgetExhausted;
	saved->owner = this;
	saved->revision = model->revision;
	saved->configuration = model->configuration;
	saved->removed = request.removed;
	saved->expanded = std::move(state.expanded_order);
	saved->reads = std::move(state.reads);
	saved->fixed = std::move(graph.fixed_bits);
	saved->topology.nodes.assign(graph.nodes.begin(), graph.nodes.end());
	saved->topology.leaves = std::move(graph.leaves);
	saved->topology.functions = std::move(graph.functions);
	snapshot.state = std::move(saved);
	return CostStatus::NoGain;
}

CostResult ModuleCost::estimate(const Request &request, int &work, const Snapshot *snapshot)
{
	std::vector<SigBit> initial;
	pool<SigBit> targets;
	if (!model->prepare(request, work, initial, targets)) return {CostStatus::BudgetExhausted};
	LutCostGraph graph(work);
	Builder::State old_state(*model, graph, request, false), new_state(*model, graph, request, true);
	if (snapshot) {
		log_assert(snapshot->state != nullptr);
		const auto &saved = *snapshot->state;
		log_assert(saved.owner == this && saved.revision == model->revision && saved.configuration == model->configuration &&
			saved.roots == initial && saved.targets == targets && saved.removed == request.removed);
		if (!spend_work(work, int64_t(GetSize(saved.topology.nodes))+GetSize(saved.expanded))) return {CostStatus::BudgetExhausted};
		graph.use_snapshot(saved.topology, saved.fixed, &saved.certificates);
		old_state.snapshot = new_state.snapshot = &saved;
		for (auto bit : saved.expanded) old_state.expand(bit);
	}
	Builder before(old_state), after(new_state);
	struct Root {
		SigBit bit;
		Signal old_signal, new_signal;
	};
	std::vector<Root> roots;
	for (auto bit : initial) {
		roots.push_back({bit, before.bit(bit), {0, 0}});
		if (!graph.valid) return {failure(work, old_state.status)};
	}
	for (auto &root : roots) {
		root.new_signal = after.bit(root.bit);
		if (!graph.valid) return {failure(work, old_state.status, new_state.status)};
	}

	pool<SigBit> modeled, rooted(initial.begin(), initial.end()), excluded = request.removed;
	for (auto bit : targets) excluded.insert(bit);
	pool<Signature> signatures;
	std::vector<SigBit> pending;
	int before_count = 0, after_count = 0;
	auto collect = [&](const Builder::State &state, int &count) {
		while (count < GetSize(state.expanded_order)) {
			if (!graph.spend()) return;
			auto bit = state.expanded_order[count++];
			if (modeled.insert(bit).second) pending.push_back(bit);
		}
	};
	auto add_root = [&](SigBit bit) {
		if (!rooted.insert(bit).second) return;
		roots.push_back({bit, before.bit(bit), after.bit(bit)});
		collect(old_state, before_count);
		collect(new_state, after_count);
	};
	collect(old_state, before_count);
	collect(new_state, after_count);
	for (int i = 0; i < GetSize(pending) && graph.spend(); i++) {
		auto bit = pending[i];
		if (model->observed(bit, modeled, excluded, work)) add_root(bit);
		if (work < 0 || !graph.valid) break;
		const auto &expr = model->expressions.at(bit);
		if (!can_share(expr)) continue;
		if (!graph.spend(GetSize(expr.inputs))) break;
		auto key = signature(expr);
		if (!signatures.insert(key).second) continue;
		auto shared = model->operators.find(key);
		if (shared == model->operators.end()) continue;
		for (auto outside : shared->second) {
			if (!graph.spend()) break;
			if (modeled.count(outside) || excluded.count(outside)) continue;
			if (model->observed(outside, modeled, excluded, work)) add_root(outside);
		}
	}
	if (work < 0 || !graph.valid) return {failure(work, old_state.status, new_state.status)};

	std::vector<int> old_roots, new_roots;
	for (int i = 0; i < GetSize(roots); i++) {
		const auto &root = roots[i];
		if (i >= GetSize(initial) && !model->observed(root.bit, modeled, excluded, work)) continue;
		graph.prepare_certificate(root.old_signal.value, root.old_signal.care);
		graph.prepare_certificate(root.new_signal.value, root.new_signal.care);
		old_roots.push_back(root.old_signal.value);
		new_roots.push_back(root.new_signal.value);
		if (!graph.valid) break;
	}
	if (work < 0 || !graph.valid) return {failure(work, old_state.status, new_state.status)};
	auto old_cover = graph.cover(old_roots);
	auto new_cover = graph.cover(new_roots);
	if (!graph.valid) return {failure(work, old_state.status, new_state.status)};
	CostResult result;
	result.retained = graph.fixed_count();
	for (int id : old_cover) {
		if (new_cover.count(id)) result.retained++;
		else result.removed++;
	}
	for (int id : new_cover) if (!old_cover.count(id)) result.added++;
	result.before = result.retained+result.removed;
	result.after = result.retained+result.added;
	result.status = result.before > result.after ? CostStatus::Profitable : CostStatus::NoGain;
	log_debug("PMUX LUT4 cover in %s %d -> %d with %d graph nodes, certificates 5/6/7=%d/%d/%d, partial functions %d, work remaining %d.\n",
		log_id(model->netlist.module()), result.before, result.after, graph.node_count(), graph.certificate_widths[5], graph.certificate_widths[6],
		graph.certificate_widths[7], graph.partial_functions, work);
	return result;
}

} // namespace PmuxLutCost
YOSYS_NAMESPACE_END
