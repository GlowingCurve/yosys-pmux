#include "kernel/yosys.h"
#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "opt_lut4_mapping.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <deque>
#include <map>
#include <set>
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static const IdString primitive = ID(cycloneiv_lcell_comb);
static const IdString chain_attr = ID(cycloneiv_carry_chain);
static const IdString index_attr = ID(cycloneiv_carry_index);
static const IdString role_attr = ID(cycloneiv_carry_role);
static const IdString bi_attr = ID(cycloneiv_carry_bi);
static const IdString x_attr = ID(cycloneiv_carry_x);

static bool generated_carry(Cell *cell)
{
	return cell->attributes.count(chain_attr) || cell->get_bool_attribute(bi_attr) || cell->get_bool_attribute(x_attr);
}

struct CarryIndex {
	SigMap sigmap;
	CellTypes types;
	dict<SigBit, pool<Cell *>> drivers;
	dict<SigBit, std::vector<std::tuple<Cell *, IdString, int>>> users;
	pool<SigBit> inputs, used, external_used, initialized;

	CarryIndex(Design *design, Module *module) : sigmap(module)
	{
		types.setup(design);
		types.setup_type(primitive, {ID(dataa), ID(datab), ID(datac), ID(datad), ID(cin)}, {ID(combout), ID(cout)}, false, true, false);
		for (auto wire : module->wires()) {
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) inputs.insert(bit);
				if (wire->port_output || wire->get_bool_attribute(ID::keep)) { used.insert(bit); external_used.insert(bit); }
				if (wire->attributes.count(ID::init)) initialized.insert(bit);
			}
		}
		for (auto cell : module->cells()) {
			for (auto &port : cell->connections()) {
				bool known = types.cell_known(cell->type);
				int offset = 0;
				for (auto bit : sigmap(port.second)) {
					if (!bit.wire) { offset++; continue; }
					if (!known || types.cell_output(cell->type, port.first)) drivers[bit].insert(cell);
					if (!known || types.cell_input(cell->type, port.first)) { used.insert(bit); users[bit].emplace_back(cell, port.first, offset); }
					offset++;
				}
			}
		}
	}

	bool legal(Cell *cell)
	{
		if (cell->has_keep_attr()) return false;
		pool<SigBit> in, out;
		for (auto &port : cell->connections()) {
			bool output = types.cell_output(cell->type, port.first);
			for (auto bit : sigmap(port.second)) {
				if (!output) {
					if (!bit.wire && bit.data != State::S0 && bit.data != State::S1) return false;
					in.insert(bit);
					continue;
				}
				if (!bit.wire || inputs.count(bit) || initialized.count(bit) || out.count(bit)) return false;
				if (!drivers.count(bit) || drivers.at(bit).size() != 1 || !drivers.at(bit).count(cell)) return false;
				out.insert(bit);
			}
		}
		for (auto bit : out) if (in.count(bit) && cell->type != ID($fa)) return false;
		return true;
	}
};

static const std::array<IdString, 5> primitive_inputs = {ID(dataa), ID(datab), ID(datac), ID(datad), ID(cin)};
using SupportCache = dict<std::vector<int>, std::array<bool, 5>>;

static State primitive_lut(uint16_t mask, std::array<State, 4> inputs)
{
	std::array<State, 16> values;
	for (int i = 0; i < 16; i++) values[i] = (mask >> i) & 1 ? State::S1 : State::S0;
	int count = 16;
	for (auto input : inputs) {
		for (int i = 0; i < count/2; i++)
			values[i] = input == State::S0 ? values[2*i] : input == State::S1 ? values[2*i+1] :
				values[2*i] == values[2*i+1] ? values[2*i] : State::Sx;
		count /= 2;
	}
	return values[0];
}

// 厂商 lut4 条件合并同时检查定义值和未定义值；同一信号的端口一起改变。
static std::array<bool, 5> primitive_support(Cell *cell, SigMap &sigmap, bool combout, bool cout, bool test_cin, SupportCache &cache)
{
	std::array<SigBit, 5> inputs;
	std::array<int, 5> variable;
	std::vector<SigBit> wires;
	int variables = 0;
	for (int port = 0; port < 5; port++) {
		log_assert(GetSize(cell->getPort(primitive_inputs[port])) == 1);
		inputs[port] = sigmap(cell->getPort(primitive_inputs[port]))[0];
		variable[port] = -1;
		if (inputs[port].wire) {
			auto found = std::find(wires.begin(), wires.end(), inputs[port]);
			if (found == wires.end()) { wires.push_back(inputs[port]); variable[port] = variables++; }
			else {
				for (int previous = 0; previous < port; previous++)
					if (inputs[previous] == inputs[port]) { variable[port] = variable[previous]; break; }
			}
		} else if ((test_cin && port == 4) || (inputs[port] != State::S0 && inputs[port] != State::S1)) {
			variable[port] = variables++;
		}
	}
	uint16_t mask = cell->getParam(ID(lut_mask)).as_int();
	bool use_cin = cell->getParam(ID(sum_lutc_input)).decode_string() == "cin";
	std::vector<int> key = {mask, use_cin, combout, cout};
	for (int port = 0; port < 5; port++)
		key.push_back(variable[port] >= 0 ? variable[port] : inputs[port] == State::S1 ? -2 : -1);
	if (cache.count(key)) return cache.at(key);
	std::array<int, 5> strides;
	int addresses = 1;
	for (int i = 0; i < variables; i++) { strides[i] = addresses; addresses *= 3; }
	std::vector<std::pair<State, State>> truth(addresses);
	for (int address = 0; address < addresses; address++) {
		std::array<State, 5> values;
		for (int port = 0; port < 5; port++) {
			int value = variable[port] < 0 ? -1 : (address / strides[variable[port]]) % 3;
			values[port] = value < 0 ? inputs[port].data : value == 0 ? State::S0 : value == 1 ? State::S1 : State::Sx;
		}
		truth[address] = {
			combout ? primitive_lut(mask, {values[0], values[1], values[use_cin ? 4 : 2], values[3]}) : State::S0,
			cout ? primitive_lut(mask, {values[0], values[1], values[4], State::S0}) : State::S0};
	}
	std::array<bool, 5> support = {};
	for (int port = 0; port < 5; port++) if (variable[port] >= 0) {
		int stride = strides[variable[port]];
		for (int address = 0; address < addresses; address++)
			if (truth[address] != truth[address - ((address / stride) % 3) * stride]) { support[port] = true; break; }
	}
	cache[key] = support;
	return support;
}

static bool specialize_generated(Design *design, Module *module, SupportCache &cache)
{
	CarryIndex index(design, module);
	bool changed = false;
	for (auto cell : module->cells().to_vector()) {
		if (!module->selected(cell) || !generated_carry(cell) || cell->has_keep_attr()) continue;
		log_assert(cell->type == primitive);
		auto live = [&](IdString port) {
			log_assert(GetSize(cell->getPort(port)) == 1);
			auto bit = index.sigmap(cell->getPort(port))[0];
			return index.used.count(bit) || index.initialized.count(bit);
		};
		bool combout = live(ID(combout)), cout = live(ID(cout));
		if (!combout && !cout) {
			module->remove(cell);
			changed = true;
			continue;
		}
		auto support = primitive_support(cell, index.sigmap, combout, cout, false, cache);
		for (int port = 0; port < 5; port++) {
			if (support[port] || port == 3) continue;
			auto previous = cell->getPort(primitive_inputs[port]);
			// 无关 CIN 使用未定义值，保留专用通道的合法入口条件。
			auto canonical = index.sigmap(previous)[0];
			SigSpec replacement(canonical == State::S0 || canonical == State::S1 ? canonical : SigBit(port == 4 ? State::Sx : State::S0));
			if (previous == replacement) continue;
			cell->setPort(primitive_inputs[port], replacement);
			changed = true;
		}
	}
	if (changed) design->scratchpad_set_bool("opt.did_something", true);
	return changed;
}

static void clean_generated(Design *design, Module *module, bool clean_logic)
{
	// opt_clean 需要 primitive 的真实端口方向；独立功能证明可以稍后读取模型。
	if (clean_logic && !design->module(primitive))
		log_error("opt_cycloneiv_carry -clean requires the Cyclone IV primitive library.\n");
	SupportCache cache;
	bool changed;
	do {
		if (clean_logic) Pass::call_on_module(design, module, "opt_clean");
		changed = specialize_generated(design, module, cache);
	} while (changed);
}

enum class CarryRole { Start, Arithmetic, Export };
struct CarryStep {
	CarryRole role;
	int bit, segment, position, initial;
	bool sum, co;
};

struct CarryPlan {
	Cell *cell;
	bool invert;
	bool remove_cell = true;
	std::string chain_name;
	SigSpec a, b, ci, x, y, co;
	SigBit bi;
	std::vector<bool> use_x, use_y, use_co;
	std::vector<CarryStep> steps;
	int arithmetic = 0, starts = 0, exports = 0, preprocessing = 0, xor_outputs = 0;
	int estimate = 0;

	int cost() const { return arithmetic + starts + exports + preprocessing + xor_outputs; }
};

// 追加一个 LE 步骤；position 在段内自增，starts/arithmetic/exports 的计数与角色一一对应。
static void add_step(CarryPlan &plan, int &segment, int &position, CarryRole role, int bit, int initial = -1)
{
	plan.steps.push_back({role, bit, segment, position++, initial,
		role == CarryRole::Arithmetic && plan.use_y[bit], role == CarryRole::Arithmetic && plan.use_co[bit]});
	if (role == CarryRole::Start) plan.starts++;
	if (role == CarryRole::Arithmetic) plan.arithmetic++;
	if (role == CarryRole::Export) plan.exports++;
}

struct CostAtom {
	int variable;
	bool invert;
};

// 删除函数中无关的输入，常量和直接连线不占用 LUT。
template<typename Truth, typename Support>
static void remove_irrelevant_inputs(Truth &truth, Support &support)
{
	for (int position = GetSize(support)-1; position >= 0; position--) {
		bool depends = false;
		for (int address = 0; address < (1 << GetSize(support)); address++)
			if (((truth >> address) & 1) != ((truth >> (address ^ (1 << position))) & 1)) depends = true;
		if (depends) continue;
		Truth reduced = 0;
		for (int address = 0; address < (1 << (GetSize(support)-1)); address++) {
			int original = (address & ((1 << position)-1)) | ((address >> position) << (position+1));
			reduced |= ((truth >> original) & 1) << address;
		}
		truth = reduced;
		support.erase(support.begin()+position);
	}
}

struct OrdinaryCost {
	dict<SigBit, int> variables;
	dict<SigBit, CostAtom> aliases;
	dict<std::pair<std::vector<int>, unsigned>, CostAtom> functions;
	int next = 1, count = 0;

	CostAtom input(SigBit bit)
	{
		if (aliases.count(bit)) return aliases.at(bit);
		if (!bit.wire) return {0, bit == State::S1};
		if (!variables.count(bit)) variables[bit] = next++;
		return {variables.at(bit), false};
	}

	CostAtom function(std::vector<CostAtom> inputs, bool carry)
	{
		std::vector<int> support;
		for (auto atom : inputs) if (atom.variable) support.push_back(atom.variable);
		std::sort(support.begin(), support.end());
		support.erase(std::unique(support.begin(), support.end()), support.end());
		unsigned truth = 0;
		for (int address = 0; address < (1 << GetSize(support)); address++) {
			std::vector<bool> values;
			for (auto atom : inputs) {
				int position = std::lower_bound(support.begin(), support.end(), atom.variable) - support.begin();
				values.push_back((atom.variable && bool(address & (1 << position))) ^ atom.invert);
			}
			bool value = carry ? (values[0] && values[1]) || (values[0] && values[2]) || (values[1] && values[2]) : false;
			if (!carry) for (auto value_bit : values) value ^= value_bit;
			if (value) truth |= 1u << address;
		}
		remove_irrelevant_inputs(truth, support);
		if (support.empty()) return {0, bool(truth)};
		if (support.size() == 1 && truth == 2) return {support[0], false};
		auto key = std::make_pair(support, truth);
		if (functions.count(key)) return functions.at(key);
		count++;
		CostAtom result = support.size() == 1 && truth == 1 ? CostAtom{support[0], true} : CostAtom{next++, false};
		functions[key] = result;
		return result;
	}
};

static int constant_bit(SigBit bit)
{
	if (bit == State::S0) return 0;
	if (bit == State::S1) return 1;
	return -1;
}

static void validate_alu(Cell *cell)
{
	log_assert(GetSize(cell->parameters) == 5 && GetSize(cell->connections()) == 7);
	for (auto param : {ID::A_WIDTH, ID::B_WIDTH, ID::Y_WIDTH, ID::A_SIGNED, ID::B_SIGNED}) {
		log_assert(cell->hasParam(param));
		auto value = cell->getParam(param);
		log_assert(value.is_fully_def() && GetSize(value) <= 32 && value.as_int() >= 0);
		if (param == ID::A_SIGNED || param == ID::B_SIGNED) log_assert(value.as_int() <= 1);
	}
	log_assert(cell->getParam(ID::A_SIGNED).as_bool() == cell->getParam(ID::B_SIGNED).as_bool());
	for (auto port : {ID::A, ID::B, ID::CI, ID::BI, ID::X, ID::Y, ID::CO}) {
		log_assert(cell->hasPort(port));
		int width = port == ID::A ? cell->getParam(ID::A_WIDTH).as_int() :
			port == ID::B ? cell->getParam(ID::B_WIDTH).as_int() :
			port == ID::CI || port == ID::BI ? 1 : cell->getParam(ID::Y_WIDTH).as_int();
		log_assert(GetSize(cell->getPort(port)) == width);
	}
}

using AuxiliaryKey = std::pair<std::vector<SigBit>, uint16_t>;

static AuxiliaryKey auxiliary_key(uint16_t mask, SigBit a, SigBit b, SigBit c)
{
	std::array<SigBit, 3> inputs = {a, b, c};
	std::vector<SigBit> support;
	for (auto bit : inputs) {
		log_assert(bit.wire || constant_bit(bit) >= 0);
		if (bit.wire) support.push_back(bit);
	}
	std::sort(support.begin(), support.end());
	support.erase(std::unique(support.begin(), support.end()), support.end());
	uint16_t truth = 0;
	for (int address = 0; address < (1 << GetSize(support)); address++) {
		int original = 0;
		for (int port = 0; port < 3; port++) {
			auto bit = inputs[port];
			int position = std::lower_bound(support.begin(), support.end(), bit) - support.begin();
			bool value = bit.wire ? bool(address & (1 << position)) : constant_bit(bit);
			original |= int(value) << port;
		}
		truth |= ((mask >> original) & 1) << address;
	}
	// 常量、重复操作数和无关输入使用同一辅助函数身份。
	remove_irrelevant_inputs(truth, support);
	uint16_t expanded = 0;
	for (int address = 0; address < 16; address++)
		expanded |= ((truth >> (address & ((1 << GetSize(support))-1))) & 1) << address;
	return {support, expanded};
}

static uint16_t x_mask(const CarryPlan &plan)
{
	return constant_bit(plan.bi) < 0 ? 0x9696 : plan.invert ? 0x9999 : 0x6666;
}

static CarryPlan make_alu_plan(Cell *cell, CarryIndex &index)
{
	CarryPlan plan;
	plan.cell = cell;
	plan.chain_name = cell->name.str();
	int width = cell->getParam(ID::Y_WIDTH).as_int();
	log_assert(width >= 0);
	plan.a = index.sigmap(cell->getPort(ID::A));
	plan.b = index.sigmap(cell->getPort(ID::B));
	plan.y = index.sigmap(cell->getPort(ID::Y));
	plan.co = index.sigmap(cell->getPort(ID::CO));
	plan.ci = index.sigmap(cell->getPort(ID::CI));
	plan.bi = index.sigmap(cell->getPort(ID::BI))[0];
	plan.invert = constant_bit(plan.bi) == 1;
	bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
	plan.a.extend_u0(width, sign);
	plan.b.extend_u0(width, sign);
	plan.x = index.sigmap(cell->getPort(ID::X));
	log_assert(GetSize(plan.a) == width && GetSize(plan.b) == width && GetSize(plan.y) == width && GetSize(plan.co) == width);
	log_assert(GetSize(plan.ci) == 1 && GetSize(plan.x) == width);
	// signed 空操作数由 $pos 扩展为 Sx，保留成熟 techmap 的未定义值语义。
	if (width == 0 || plan.a.has_const(State::Sx) || plan.b.has_const(State::Sx)) return plan;
	int last = -1;
	pool<AuxiliaryKey> preprocessing, xor_outputs;
	for (int i = 0; i < width; i++) {
		plan.use_y.push_back(index.used.count(plan.y[i]));
		plan.use_co.push_back(index.used.count(plan.co[i]));
		plan.use_x.push_back(index.used.count(plan.x[i]));
		if (plan.use_y.back() || plan.use_co.back()) last = i;
		if (plan.use_x.back()) xor_outputs.insert(auxiliary_key(x_mask(plan), plan.a[i], plan.b[i], plan.bi));
	}
	int segment = 0, position = 0;
	bool external = false;
	for (int i = 0; i <= last; i++) {
		int initial = i == 0 ? constant_bit(plan.ci[0]) : -1;
		if (position == 0 && initial < 0) add_step(plan, segment, position, CarryRole::Start, i);
		int required = 1 + int(plan.use_y[i] && plan.use_co[i]);
		// 每段预留一个 LE，以便将段尾 carry 导出到普通互连。
		if (position + required + int(i < last) > 16) {
			if (!external) add_step(plan, segment, position, CarryRole::Export, i-1);
			log_assert(position <= 16);
			segment++;
			position = 0;
			add_step(plan, segment, position, CarryRole::Start, i);
			initial = -1;
		}
		add_step(plan, segment, position, CarryRole::Arithmetic, i, initial);
		external = !plan.use_y[i];
		if (plan.use_y[i] && plan.use_co[i]) { add_step(plan, segment, position, CarryRole::Export, i); external = true; }
		if (constant_bit(plan.bi) < 0) preprocessing.insert(auxiliary_key(0x6666, plan.b[i], plan.bi, State::S0));
		log_assert(position <= 16);
	}
	plan.preprocessing = GetSize(preprocessing);
	for (auto &key : xor_outputs) if (!preprocessing.count(key)) plan.xor_outputs++;
	OrdinaryCost baseline;
	CostAtom carry = baseline.input(plan.ci[0]);
	for (int i = 0; i < width; i++) {
		auto a = baseline.input(plan.a[i]), b = baseline.input(plan.b[i]);
		if (plan.invert) b.invert = !b.invert;
		if (constant_bit(plan.bi) < 0 && (i <= last || plan.use_x[i]))
			b = baseline.function({b, baseline.input(plan.bi)}, false);
		if (plan.use_x[i]) baseline.function({a, b}, false);
		if (i > last) continue;
		if (plan.use_y[i]) baseline.function({a, b, carry}, false);
		if (i < last || plan.use_co[i]) carry = baseline.function({a, b, carry}, true);
	}
	plan.estimate = baseline.count;
	return plan;
}

static uint16_t arithmetic_mask(int initial, bool invert, bool sum)
{
	uint16_t mask = 0;
	for (int address = 0; address < 16; address++) {
		bool a = address & 1, b = bool(address & 2) ^ invert;
		bool c = initial < 0 ? bool(address & 4) : bool(initial);
		bool carry = (a && b) || (a && c) || (b && c);
		bool value = (address & 8) && sum ? a ^ b ^ c : carry;
		if (value) mask |= uint16_t(1) << address;
	}
	return mask;
}

// 输入和输出反相全部吸收到算术真值表，专用通道保持直接连接。
static uint16_t lut_arithmetic_mask(int initial, int phase, bool invert_sum, bool invert_carry, bool sum = true)
{
	uint16_t mask = 0;
	for (int address = 0; address < 16; address++) {
		bool a = bool(address & 1) ^ bool(phase & 1);
		bool b = bool(address & 2) ^ bool(phase & 2);
		bool c = (initial < 0 ? bool(address & 4) : bool(initial)) ^ bool(phase & 4);
		bool carry = ((a && b) || (a && c) || (b && c)) ^ invert_carry;
		bool value = (address & 8) && sum ? (a ^ b ^ c ^ invert_sum) : carry;
		if (value) mask |= uint16_t(1) << address;
	}
	return mask;
}

struct CarryEmitter {
	Module *module;
	CarryPlan &plan;
	dict<AuxiliaryKey, Cell *> auxiliary;
	int emitted = 0;

	CarryEmitter(Module *module, CarryPlan &plan) : module(module), plan(plan) {}
	SigBit wire() { return SigBit(module->addWire(NEW_ID)); }
	Cell *emit(uint16_t mask, SigBit a, SigBit b, SigBit c, SigBit ci, SigBit out, SigBit carry, bool arithmetic)
	{
		auto cell = module->addCell(NEW_ID, primitive);
		cell->setParam(ID(lut_mask), Const(mask, 16));
		cell->setParam(ID(sum_lutc_input), Const(arithmetic ? "cin" : "datac"));
		cell->setParam(ID(dont_touch), Const("on"));
		cell->setParam(ID(lpm_type), Const("cycloneiv_lcell_comb"));
		cell->setPort(ID(dataa), a);
		cell->setPort(ID(datab), b);
		cell->setPort(ID(datac), c);
		cell->setPort(ID(datad), State::S1);
		cell->setPort(ID(cin), ci);
		cell->setPort(ID(combout), out);
		cell->setPort(ID(cout), carry);
		cell->attributes[ID(cycloneiv_carry_mask)] = Const(mask, 16);
		if (plan.cell->attributes.count(ID::src)) cell->attributes[ID::src] = plan.cell->attributes.at(ID::src);
		emitted++;
		return cell;
	}

	SigBit emit_auxiliary(const AuxiliaryKey &key, bool bi, SigBit output)
	{
		Cell *cell;
		if (auxiliary.count(key)) {
			cell = auxiliary.at(key);
			if (output.wire) module->connect(output, cell->getPort(ID(combout)));
		} else {
			if (!output.wire) output = wire();
			std::array<SigBit, 3> inputs = {State::S0, State::S0, State::S0};
			for (int i = 0; i < GetSize(key.first); i++) inputs[i] = key.first[i];
			cell = emit(key.second, inputs[0], inputs[1], inputs[2], State::Sx, output, wire(), false);
			auxiliary[key] = cell;
		}
		cell->set_bool_attribute(bi ? bi_attr : x_attr);
		cell->attributes[role_attr] = Const(cell->get_bool_attribute(bi_attr) && cell->get_bool_attribute(x_attr) ? "bi_x" : bi ? "bi" : "x");
		return cell->getPort(ID(combout))[0];
	}

	SigBit operand_b(int bit)
	{
		auto b = plan.b[bit];
		if (constant_bit(plan.bi) >= 0) return b;
		return emit_auxiliary(auxiliary_key(0x6666, b, plan.bi, State::S0), true, State::Sx);
	}

	void run()
	{
		SigBit carry = State::Sx, external = State::Sx;
		for (auto &step : plan.steps) {
			SigBit out = wire(), next = wire();
			Cell *cell;
			if (step.role == CarryRole::Start) {
				auto input = step.position == 0 && step.segment > 0 ? external : plan.ci[0];
				cell = emit(0xaaaa, input, State::S0, State::S0, State::Sx, out, next, true);
				cell->attributes[role_attr] = Const("start");
			} else if (step.role == CarryRole::Export) {
				out = plan.use_co[step.bit] ? plan.co[step.bit] : out;
				cell = emit(0xf0f0, State::S0, State::S0, State::S0, carry, out, next, true);
				external = out;
				cell->attributes[role_attr] = Const("export");
			} else {
				if (step.sum) out = plan.y[step.bit];
				else if (step.co) out = plan.co[step.bit];
				auto ci = step.initial >= 0 ? SigBit(State::Sx) : carry;
				cell = emit(arithmetic_mask(step.initial, plan.invert, step.sum), plan.a[step.bit], operand_b(step.bit), State::S0, ci, out, next, true);
				if (!step.sum) external = out;
				cell->attributes[role_attr] = Const(step.initial >= 0 ? "first" : "arithmetic");
			}
			cell->attributes[chain_attr] = Const(stringf("%s:%d", plan.chain_name, step.segment));
			cell->attributes[index_attr] = Const(step.position);
			carry = next;
		}
		for (int i = 0; i < GetSize(plan.x); i++) if (plan.use_x[i]) {
			emit_auxiliary(auxiliary_key(x_mask(plan), plan.a[i], plan.b[i], plan.bi), false, plan.x[i]);
		}
		log_assert(emitted == plan.cost());
		if (plan.remove_cell) module->remove(plan.cell);
	}
};

struct FaBit {
	Cell *cell;
	int offset, previous = -1, next = -1, ciport = 2;
	std::array<SigBit, 3> inputs;
	SigBit sum, carry;
};

static void map_fa_chains(Design *design, Module *module, bool force)
{
	CarryIndex index(design, module);
	std::vector<FaBit> nodes;
	dict<SigBit, int> carry_node;
	for (auto cell : module->selected_cells()) {
		if (cell->type != ID($fa) || !index.legal(cell)) continue;
		int width = cell->getParam(ID::WIDTH).as_int();
		log_assert(width > 0);
		std::array<SigSpec, 3> inputs = {index.sigmap(cell->getPort(ID::A)), index.sigmap(cell->getPort(ID::B)), index.sigmap(cell->getPort(ID::C))};
		auto sum = index.sigmap(cell->getPort(ID::Y)), carry = index.sigmap(cell->getPort(ID::X));
		log_assert(GetSize(inputs[0]) == width && GetSize(inputs[1]) == width && GetSize(inputs[2]) == width && GetSize(sum) == width && GetSize(carry) == width);
		for (int i = 0; i < width; i++) {
			FaBit node;
			node.cell = cell;
			node.offset = i;
			node.inputs = {inputs[0][i], inputs[1][i], inputs[2][i]};
			node.sum = sum[i]; node.carry = carry[i];
			bool self_feedback = false;
			for (auto input : node.inputs) if (input == node.sum || input == node.carry) self_feedback = true;
			if (self_feedback) continue;
			carry_node[node.carry] = GetSize(nodes);
			nodes.push_back(node);
		}
	}
	// 全加器输入对称；选择唯一 carry 后继，其余使用者通过普通输出连接。
	for (int i = 0; i < GetSize(nodes); i++) for (int port = 0; port < 3; port++) {
		if (nodes[i].previous >= 0 || !carry_node.count(nodes[i].inputs[port])) continue;
		int predecessor = carry_node.at(nodes[i].inputs[port]);
		if (predecessor == i || nodes[predecessor].next >= 0) continue;
		bool cycle = false;
		for (int successor = i; successor >= 0; successor = nodes[successor].next)
			if (successor == predecessor) cycle = true;
		if (cycle) continue;
		nodes[i].previous = predecessor;
		nodes[i].ciport = port;
		nodes[predecessor].next = i;
	}
	dict<Cell *, pool<int>> mapped;
	for (int root = 0; root < GetSize(nodes); root++) {
		if (nodes[root].previous >= 0) continue;
		std::vector<int> chain;
		for (int current = root; current >= 0; current = nodes[current].next) chain.push_back(current);
		CarryPlan plan;
		plan.cell = nodes[root].cell;
		plan.chain_name = stringf("%s[%d]", plan.cell->name.c_str(), nodes[root].offset);
		plan.invert = false; plan.remove_cell = false; plan.bi = State::S0;
		plan.ci = nodes[root].inputs[nodes[root].ciport];
		for (int current : chain) {
			auto &node = nodes[current];
			std::vector<SigBit> operands;
			for (int port = 0; port < 3; port++) if (port != node.ciport) operands.push_back(node.inputs[port]);
			plan.a.append(operands[0]); plan.b.append(operands[1]); plan.y.append(node.sum); plan.co.append(node.carry);
			plan.use_y.push_back(index.used.count(node.sum)); plan.use_x.push_back(false);
			bool ordinary = index.external_used.count(node.carry);
			for (auto &use : index.users[node.carry]) {
				bool dedicated = false;
				if (node.next >= 0) {
					auto &successor = nodes[node.next];
					IdString port = std::array<IdString, 3>{ID::A, ID::B, ID::C}[successor.ciport];
					dedicated = std::get<0>(use) == successor.cell && std::get<1>(use) == port && std::get<2>(use) == successor.offset;
				}
				if (!dedicated) ordinary = true;
			}
			plan.use_co.push_back(ordinary);
		}
		int position = 0, segment = 0;
		bool external = false;
		OrdinaryCost baseline;
		CostAtom carry = baseline.input(plan.ci[0]);
		for (int i = 0; i < GetSize(chain); i++) {
			int initial = i == 0 ? constant_bit(plan.ci[0]) : -1;
			if (i == 0 && initial < 0) add_step(plan, segment, position, CarryRole::Start, i);
			int required = 1 + int(plan.use_y[i] && plan.use_co[i]);
			if (position + required + int(i+1 < GetSize(chain)) > 16) {
				if (!external) add_step(plan, segment, position, CarryRole::Export, i-1);
				log_assert(position <= 16);
				segment++; position = 0; add_step(plan, segment, position, CarryRole::Start, i); initial = -1;
			}
			add_step(plan, segment, position, CarryRole::Arithmetic, i, initial);
			external = !plan.use_y[i];
			if (plan.use_y[i] && plan.use_co[i]) { add_step(plan, segment, position, CarryRole::Export, i); external = true; }
			auto a = baseline.input(plan.a[i]), b = baseline.input(plan.b[i]);
			if (plan.use_y[i]) baseline.aliases[plan.y[i]] = baseline.function({a,b,carry}, false);
			if (i+1 < GetSize(chain) || plan.use_co[i]) {
				carry = baseline.function({a,b,carry}, true);
				baseline.aliases[plan.co[i]] = carry;
			}
		}
		plan.estimate = baseline.count;
		if (!force && plan.cost() >= plan.estimate) continue;
		if (!index.used.count(nodes[chain.back()].sum) && !index.used.count(nodes[chain.back()].carry)) continue;
		log("Mapping FA chain rooted at %s.%s[%d]: %d arithmetic + %d start + %d export = %d LEs; ordinary-LUT estimate %d.\n",
			log_id(module), log_id(plan.cell), nodes[root].offset, plan.arithmetic, plan.starts, plan.exports, plan.cost(), plan.estimate);
		CarryEmitter(module, plan).run();
		for (int current : chain) mapped[nodes[current].cell].insert(nodes[current].offset);
	}
	for (auto &entry : mapped) {
		auto cell = entry.first;
		int width = cell->getParam(ID::WIDTH).as_int();
		if (GetSize(entry.second) == width) { module->remove(cell); continue; }
		for (auto port : {ID::A, ID::B, ID::C, ID::X, ID::Y}) {
			auto previous = cell->getPort(port);
			SigSpec retained;
			for (int i = 0; i < width; i++) if (!entry.second.count(i)) retained.append(previous[i]);
			cell->setPort(port, retained);
		}
		cell->setParam(ID::WIDTH, Const(width-GetSize(entry.second)));
	}
}

static void audit_carry(Design *design, Module *module)
{
	CarryIndex index(design, module);
	dict<std::string, dict<int, Cell *>> chains;
	pool<SigBit> ordinary;
	std::vector<Cell *> auxiliary;
	SupportCache cache;
	int first = 0, arithmetic = 0, starts = 0, exports = 0, bi_only = 0, x_only = 0, shared = 0;
	int physical_chains = 0;
	int native = 0, generic = 0, inverters = 0;
	for (auto wire : module->wires()) if (wire->port_id || wire->get_bool_attribute(ID::keep))
		for (auto bit : index.sigmap(wire)) ordinary.insert(bit);
	for (auto cell : module->cells()) {
		if (cell->type == primitive) native++;
		if (cell->type == ID($lut)) generic++;
		if (cell->type.in(ID($not), ID($_NOT_))) inverters += GetSize(cell->getPort(ID::Y));
		bool bi = cell->get_bool_attribute(bi_attr), x = cell->get_bool_attribute(x_attr);
		if (!cell->attributes.count(chain_attr) && !bi && !x) continue;
		if (cell->type != primitive) log_error("Cyclone IV carry primitive boundary changed at %s.%s.\n", log_id(module), log_id(cell));
		if (GetSize(cell->parameters) != 4 || GetSize(cell->connections()) != 7)
			log_error("Cyclone IV carry primitive interface changed.\n");
		for (auto port : {ID(dataa), ID(datab), ID(datac), ID(datad), ID(cin), ID(combout), ID(cout)})
			if (!cell->hasPort(port) || GetSize(cell->getPort(port)) != 1)
				log_error("Cyclone IV carry primitive port changed.\n");
		if (cell->getParam(ID(lut_mask)) != cell->attributes.at(ID(cycloneiv_carry_mask)) ||
			GetSize(cell->getParam(ID(lut_mask))) != 16 || !cell->getParam(ID(lut_mask)).is_fully_def() ||
			cell->getParam(ID(dont_touch)).decode_string() != "on" ||
			cell->getParam(ID(lpm_type)).decode_string() != "cycloneiv_lcell_comb")
			log_error("Cyclone IV carry primitive parameters changed.\n");
		if (bi || x) {
			if (cell->attributes.count(chain_attr) || cell->attributes.count(index_attr) ||
				cell->attributes.at(role_attr).decode_string() != (bi && x ? "bi_x" : bi ? "bi" : "x"))
				log_error("Cyclone IV auxiliary roles changed.\n");
			if (bi && x) shared++;
			else if (bi) bi_only++;
			else x_only++;
			auxiliary.push_back(cell);
			continue;
		}
		auto role = cell->attributes.at(role_attr).decode_string();
		if (role == "first" || role == "lut_first") first++;
		else if (role == "arithmetic" || role == "lut_arithmetic") arithmetic++;
		else if (role == "start") starts++;
		else if (role == "export") exports++;
		else log_error("Invalid Cyclone IV carry role.\n");
		int mask = cell->getParam(ID(lut_mask)).as_int();
		bool valid_mask = role == "start" ? mask == 0xaaaa : role == "export" ? mask == 0xf0f0 : false;
		if (role == "first" || role == "arithmetic")
			for (int initial : {-1, 0, 1}) for (bool invert : {false, true}) for (bool sum : {false, true})
				if ((role == "first" ? initial >= 0 : initial == -1) && mask == arithmetic_mask(initial, invert, sum)) valid_mask = true;
		if (role == "lut_first" || role == "lut_arithmetic")
			for (int initial : {-1, 0, 1}) for (int phase = 0; phase < 8; phase++)
				for (bool invert_sum : {false, true}) for (bool invert_carry : {false, true}) for (bool sum : {false, true})
					if ((role == "lut_first" ? initial >= 0 : initial == -1) &&
						mask == lut_arithmetic_mask(initial, phase, invert_sum, invert_carry, sum)) valid_mask = true;
		if (!valid_mask) log_error("Cyclone IV carry mask does not match its role.\n");
		auto chain = cell->attributes.at(chain_attr).decode_string();
		int position = cell->attributes.at(index_attr).as_int();
		if (position < 0 || position >= 16 || chains[chain].count(position)) log_error("Invalid Cyclone IV carry chain position.\n");
		chains[chain][position] = cell;
	}
	for (auto cell : auxiliary) {
		if (cell->getParam(ID(sum_lutc_input)).decode_string() != "datac" ||
			cell->getPort(ID(datad)) != SigSpec(State::S1) || index.sigmap(cell->getPort(ID(cin)))[0].wire)
			log_error("Cyclone IV auxiliary parameters changed.\n");
		int mask = cell->getParam(ID(lut_mask)).as_int();
		int parity = 0;
		for (int port = 0; port < 3; port++)
			if (bool(mask & 1) != bool((mask >> (1 << port)) & 1)) parity |= 1 << port;
		for (int address = 0; address < 16; address++) {
			bool value = mask & 1;
			for (int port = 0; port < 3; port++) if (parity & (1 << port)) value ^= bool(address & (1 << port));
			if (bool((mask >> address) & 1) != value) log_error("Cyclone IV auxiliary XOR function changed.\n");
		}
		if (cell->get_bool_attribute(bi_attr) && !cell->get_bool_attribute(x_attr) && (parity & 4)) log_error("Cyclone IV BI preprocessing has excess support.\n");
		auto cout = index.sigmap(cell->getPort(ID(cout)))[0], out = index.sigmap(cell->getPort(ID(combout)))[0];
		if (!cout.wire || ordinary.count(cout) || !index.users[cout].empty() ||
			!index.drivers.count(cout) || index.drivers.at(cout).size() != 1 || !index.drivers.at(cout).count(cell) ||
			!out.wire || index.inputs.count(out) || !index.drivers.count(out) || index.drivers.at(out).size() != 1 || !index.drivers.at(out).count(cell))
			log_error("Cyclone IV auxiliary output ownership changed.\n");
	}
	for (auto &entry : chains) {
		auto &chain = entry.second;
		for (auto &position : chain) {
			int i = position.first;
			auto cell = position.second;
			if (cell->getParam(ID(sum_lutc_input)).decode_string() != "cin" || cell->getPort(ID(datad)) != SigSpec(State::S1))
				log_error("Cyclone IV arithmetic parameters changed.\n");
			auto cin = index.sigmap(cell->getPort(ID(cin)))[0];
			auto cout = index.sigmap(cell->getPort(ID(cout)))[0];
			auto out = index.sigmap(cell->getPort(ID(combout)))[0];
			if (!out.wire || index.inputs.count(out) || !index.drivers.count(out) || index.drivers.at(out).size() != 1 || !index.drivers.at(out).count(cell))
				log_error("Cyclone IV COMBout has an illegal driver.\n");
			if (!cout.wire || ordinary.count(cout) || !index.drivers.count(cout) || index.drivers.at(cout).size() != 1 || !index.drivers.at(cout).count(cell))
				log_error("Cyclone IV COUT has an illegal driver or ordinary routing use.\n");
			if (!cin.wire) {
				physical_chains++;
				bool combout = index.used.count(out) || index.initialized.count(out);
				bool carry_out = index.used.count(cout) || index.initialized.count(cout);
				if (cell->has_keep_attr()) combout = carry_out = true;
				if (primitive_support(cell, index.sigmap, combout, carry_out, true, cache)[4])
					log_error("Cyclone IV chain entry depends on CIN.\n");
			} else if (i == 0 || !chain.count(i-1) || cin != index.sigmap(chain.at(i-1)->getPort(ID(cout)))[0])
				log_error("Cyclone IV CIN does not follow the preceding LE COUT.\n");
			auto &fanout = index.users[cout];
			if (!fanout.empty()) {
				if (!chain.count(i+1) || GetSize(fanout) != 1 || std::get<0>(fanout[0]) != chain.at(i+1) || std::get<1>(fanout[0]) != ID(cin))
					log_error("Cyclone IV COUT must drive exactly one adjacent CIN.\n");
			}
		}
	}
	log("Audited %d Cyclone IV carry chains in %s.\n", physical_chains, log_id(module));
	log("Cyclone IV physical area in %s: native=%d generic-LUT=%d inverter-bits=%d total=%d; carry first=%d arithmetic=%d start=%d export=%d auxiliary BI-only=%d X-only=%d shared-BI-X=%d generated=%d.\n",
		log_id(module), native, generic, inverters, native + generic + inverters, first, arithmetic, starts, exports,
		bi_only, x_only, shared, first + arithmetic + starts + exports + bi_only + x_only + shared);
}

#include "opt_cycloneiv_lut_carry.h"

struct OptCycloneivCarryPass : Pass {
	OptCycloneivCarryPass() : Pass("opt_cycloneiv_carry", "map arithmetic to bounded Cyclone IV carry chains") {}
	void help() override
	{
		log("\n    opt_cycloneiv_carry [-force] [-clean] [-check] [selection]\n");
		log("    opt_cycloneiv_carry -lut [budget options] [selection]\n\n");
		log("Map selected $alu and profitable $fa cells to cycloneiv_lcell_comb.\n");
		log("Run after alumacc and before generic techmap. Dynamic carry inputs use\n");
		log("a carry-start LE; all ordinary carry outputs use COMBout. Carry chains\n");
		log("contain at most 16 LEs, including start and export/forward cells.\n");
		log("\n    -force\n        Bypass the ordinary-LUT area estimate for independent verification.\n");
		log("\n    -check\n        Audit existing generated carry chains without mapping cells.\n");
		log("\n    -clean\n        Clean existing generated cells and unused input cones to a fixed point.\n");
		log("        Requires the primitive library; combine with -check to audit the result.\n");
		log("\nThe cost estimate includes every emitted primitive. Final area acceptance\n");
		log("requires complete mapping of the surrounding design. Functional proofs\n");
		log("must use the independent complete Altera primitive model.\n");
		log("Auxiliary BI and X attributes mark each physical LE; shared BI/X functions\n");
		log("carry both attributes and role bi_x. Audit totals count shared LEs once.\n\n");
		log("    -lut\n        Recognize XOR3/majority pairs in mapped $lut/NOT networks.\n");
		log("        Run after ABC9 and LUT postprocessing, before map_cells.\n");
		log("        Commit only a strict reduction using the complete deletion closure.\n");
		log("    -max-cuts N\n    -max-pairs N\n    -max-work N\n");
		log("    -max-memory N\n    -max-proof N\n");
		log("        Design-wide limits; memory is bytes and proof counts truth operations.\n");
		log("        Defaults scale with LUT count and have fixed upper bounds.\n");
		log("        Explicit zero ends the search. -lut does not accept -force.\n\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		bool force = false, check = false, clean = false, lut = false;
		LutCarryOptions lut_options;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-force") force = true;
			else if (args[argidx] == "-check") check = true;
			else if (args[argidx] == "-clean") clean = true;
			else if (args[argidx] == "-lut") lut = true;
			else if (lut_options.parse(args, argidx)) {}
			else break;
		}
		extra_args(args, argidx, design);
		log_header(design, "Executing OPT_CYCLONEIV_CARRY pass.\n");
		if (lut) {
			if (force || clean || check) log_cmd_error("opt_cycloneiv_carry -lut requires a separate mapping invocation.\n");
			map_lut_carry(design, lut_options);
			return;
		}
		if (lut_options.explicit_limits) log_cmd_error("LUT carry budgets require -lut.\n");
		for (auto module : design->selected_modules()) {
			if (module->get_blackbox_attribute() || module->has_processes()) continue;
			if (clean && !design->selected_whole_module(module))
				log_cmd_error("opt_cycloneiv_carry -clean requires whole-module selection.\n");
			if (clean) audit_carry(design, module);
			if (!check && !clean) {
				CarryIndex index(design, module);
				for (auto cell : module->selected_cells()) {
					if (cell->type != ID($alu)) continue;
					validate_alu(cell);
					if (!index.legal(cell)) continue;
					auto plan = make_alu_plan(cell, index);
					if (plan.steps.empty() || (!force && plan.cost() >= plan.estimate)) continue;
					log("Mapping %s.%s: %d arithmetic + %d start + %d export + %d BI + %d X = %d LEs; ordinary-LUT estimate %d.\n",
						log_id(module), log_id(cell), plan.arithmetic, plan.starts, plan.exports, plan.preprocessing, plan.xor_outputs, plan.cost(), plan.estimate);
					CarryEmitter(module, plan).run();
				}
				map_fa_chains(design, module, force);
			}
			if (!check || clean) clean_generated(design, module, clean);
			audit_carry(design, module);
		}
	}
} OptCycloneivCarryPass;

PRIVATE_NAMESPACE_END
