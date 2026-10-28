// opt_pmuxstate 按控制条件化简触发器输入，并将独热寄存器组转换为编码状态和共享数据寄存器。
// 共享状态选择和数据存储，减少重复的触发器与组合选择逻辑。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "passes/opt/pmux_celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxStateWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	FfInitVals initvals;
	PmuxCellTypes types;
	dict<SigBit, Cell *> drivers;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> protected_bits, kept_bits, conflicted, input_bits;
	pool<Cell *> removed;
	int budget = 262144;

	PmuxStateWorker(Module *module, Design *design) : module(module), design(design), sigmap(module), initvals(&sigmap, module), types(module, design)
	{
		for (auto wire : module->wires()) {
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) {
					drivers[bit] = nullptr;
					input_bits.insert(bit);
				}
				if (wire->port_output || wire->get_bool_attribute(ID::keep)) protected_bits.insert(bit);
				if (wire->get_bool_attribute(ID::keep)) kept_bits.insert(bit);
			}
		}
		for (auto cell : module->cells()) for (auto &port : cell->connections()) {
			bool input = types.cell_input(cell->type, port.first), output = types.cell_output(cell->type, port.first);
			for (auto bit : sigmap(port.second)) {
				if (output) {
					if (drivers.count(bit)) {
						drivers[bit] = nullptr;
						conflicted.insert(bit);
					} else {
						drivers[bit] = cell;
					}
				}
				if (input || !output) users[bit].insert(cell);
				if ((!input && !output) || cell->get_bool_attribute(ID::keep)) {
					protected_bits.insert(bit);
					kept_bits.insert(bit);
					if (!input && !output) {
						drivers[bit] = nullptr;
						conflicted.insert(bit);
					}
				}
			}
		}
	}

	Cell *driver(SigBit bit)
	{
		if (!bit.wire) return nullptr;
		auto found = drivers.find(bit);
		if (found == drivers.end()) return nullptr;
		auto cell = found->second;
		return removed.count(cell) ? nullptr : cell;
	}

	bool editable(Cell *cell, IdString port = ID::Y)
	{
		if (!cell || removed.count(cell) || !design->selected(module, cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(port)) return false;
		for (auto bit : sigmap(cell->getPort(port))) if (!bit.wire || kept_bits.count(bit) || driver(bit) != cell) return false;
		return true;
	}

	bool spend(int amount)
	{
		budget -= amount;
		return budget >= 0;
	}

	bool fact(dict<SigBit, State> &facts, SigBit bit, State value)
	{
		if (!bit.wire) return bit.data == value;
		if (kept_bits.count(bit) || conflicted.count(bit) || (!driver(bit) && !input_bits.count(bit))) return true;
		auto found = facts.find(bit);
		if (found != facts.end()) return found->second == value;
		facts[bit] = value;
		return true;
	}

	bool condition(SigBit bit, bool value, dict<SigBit, State> &facts, int depth = 0)
	{
		if (depth > 8 || !spend(1)) return false;
		if (!bit.wire) return bit.data == (value ? State::S1 : State::S0);
		auto cell = driver(bit);
		if (!cell || !cell->hasPort(ID::Y) || sigmap(cell->getPort(ID::Y)) != SigSpec(bit)) return true;
		if (!cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($not), ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($logic_and), ID($logic_or))) return true;
		auto a = sigmap(cell->getPort(ID::A));
		if (GetSize(a) > 256 || !spend(GetSize(a))) return false;
		if ((cell->type == ID($logic_not) && value) || (cell->type.in(ID($reduce_or), ID($reduce_bool)) && !value) || (cell->type == ID($reduce_and) && value)) {
			State constant = cell->type == ID($reduce_and) ? State::S1 : State::S0;
			for (auto input : a) if (!fact(facts, input, constant)) return false;
		} else if (cell->type.in(ID($logic_not), ID($not)) && GetSize(a) == 1) {
			return condition(a[0], !value, facts, depth + 1);
		} else if ((cell->type == ID($eq) && value) || (cell->type == ID($ne) && !value)) {
			if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool()) return true;
			auto b = sigmap(cell->getPort(ID::B));
			if (GetSize(b) > 256 || !spend(GetSize(b))) return false;
			if (a.is_fully_const()) std::swap(a, b);
			if (!b.is_fully_def()) return true;
			int width = std::max(GetSize(a), GetSize(b));
			a.extend_u0(width);
			b.extend_u0(width);
			for (int i = 0; i < width; i++) if (!fact(facts, a[i], b[i].data)) return false;
		} else if ((cell->type == ID($logic_and) && value) || (cell->type == ID($logic_or) && !value)) {
			auto b = sigmap(cell->getPort(ID::B));
			if (GetSize(a) == 1 && GetSize(b) == 1) return condition(a[0], value, facts, depth + 1) && condition(b[0], value, facts, depth + 1);
		}
		return true;
	}

	void specialize(Cell *cell)
	{
		if (!editable(cell) || !cell->type.in(ID($mux), ID($pmux))) return;
		auto s = sigmap(cell->getPort(ID::S));
		int width = GetSize(cell->getPort(ID::A));
		if (width > 4096 || GetSize(s) > 16 || !spend(width * GetSize(s))) return;
		int branches = cell->type == ID($mux) ? 2 : GetSize(s);
		for (int index = 0; index < branches; index++) {
			IdString port = cell->type == ID($mux) && index == 0 ? ID::A : ID::B;
			int offset = cell->type == ID($pmux) ? index * width : 0;
			dict<SigBit, State> facts;
			if (!condition(cell->type == ID($mux) ? s[0] : s[index], cell->type == ID($pmux) || index != 0, facts)) continue;
			auto signal = cell->getPort(port);
			for (int i = offset; i < offset + width; i++) {
				auto bit = sigmap(signal[i]);
				if (facts.count(bit)) signal[i] = facts.at(bit);
			}
			if (!sigmap(signal.extract(offset, width)).is_fully_def()) continue;
			cell->setPort(port, signal);
		}
	}

	bool onehot(const Const &value)
	{
		if (!value.is_fully_def()) return false;
		int count = 0;
		for (auto bit : value) count += bit == State::S1;
		return count == 1;
	}

	bool ff_type(Cell *cell)
	{
		return cell && cell->type.in(ID($dff), ID($dffe), ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce));
	}

	bool permutation(const SigSpec &d, const SigSpec &q)
	{
		if (GetSize(d) != GetSize(q)) return false;
		pool<SigBit> expected(q.begin(), q.end()), actual(d.begin(), d.end());
		return GetSize(expected) == GetSize(q) && actual == expected;
	}

	void decode_onehot(Cell *cell)
	{
		if (!editable(cell) || !cell->type.in(ID($eq), ID($logic_not)) || GetSize(cell->getPort(ID::Y)) != 1) return;
		auto q = sigmap(cell->getPort(ID::A));
		SigSpec constant = cell->type == ID($logic_not) ? SigSpec(State::S0, GetSize(q)) : sigmap(cell->getPort(ID::B));
		if (q.is_fully_const()) std::swap(q, constant);
		if (GetSize(q) < 2 || GetSize(q) > 64 || !constant.is_fully_def() || GetSize(constant) > GetSize(q) || !spend(GetSize(q))) return;
		if (cell->type == ID($eq) && (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())) return;
		constant.extend_u0(GetSize(q));
		if (!onehot(constant.as_const())) return;
		auto state = driver(q[0]);
		if (!ff_type(state) || !editable(state, ID::Q)) return;
		FfData ff(&initvals, state);
		if (!ff.has_clk || ff.has_aload || ff.has_sr || sigmap(ff.sig_q) != q || !onehot(ff.val_init)) return;
		if ((ff.has_arst && !onehot(ff.val_arst)) || (ff.has_srst && !onehot(ff.val_srst))) return;
		if (!permutation(sigmap(ff.sig_d), q)) return;
		// 初始条件与每种 reset 均为 onehot；双射置换和 enable 保持使不变量逐步成立。
		int index = 0;
		while (constant[index] != State::S1) index++;
		module->connect(cell->getPort(ID::Y), q[index]);
		removed.insert(cell);
	}

	struct Decode {
		Cell *cell = nullptr;
		SigSpec signal;
		int value = -1;
	};

	Decode decode(SigBit bit)
	{
		Decode result;
		auto cell = driver(bit);
		if (!cell || !cell->hasPort(ID::Y) || sigmap(cell->getPort(ID::Y)) != SigSpec(bit)) return result;
		if (!cell->type.in(ID($eq), ID($logic_not))) return result;
		auto signal = sigmap(cell->getPort(ID::A));
		SigSpec constant = cell->type == ID($logic_not) ? SigSpec(State::S0, GetSize(signal)) : sigmap(cell->getPort(ID::B));
		if (signal.is_fully_const()) std::swap(signal, constant);
		if (signal.empty() || GetSize(signal) > 4 || !constant.is_fully_def() || GetSize(constant) > GetSize(signal)) return result;
		if (cell->type == ID($eq) && (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())) return result;
		constant.extend_u0(GetSize(signal));
		result.cell = cell;
		result.signal = signal;
		result.value = constant.as_int();
		return result;
	}

	bool private_to(const SigSpec &signal, const pool<Cell *> &allowed)
	{
		for (auto bit : signal) {
			if (!bit.wire || protected_bits.count(bit) || conflicted.count(bit)) return false;
			for (auto user : users[bit]) if (!removed.count(user) && !allowed.count(user)) return false;
		}
		return true;
	}

	void compress(Cell *cell)
	{
		if (!editable(cell) || cell->type != ID($pmux)) return;
		auto s = sigmap(cell->getPort(ID::S)), b = sigmap(cell->getPort(ID::B));
		int count = GetSize(s), width = GetSize(cell->getPort(ID::A));
		if (count < 2 || count > 16 || width > 4096 || !sigmap(cell->getPort(ID::A)).is_fully_undef() || !spend(count * width)) return;
		std::vector<Decode> selects;
		pool<Cell *> old_cells = {cell};
		pool<int> values;
		SigSpec state_q;
		for (auto bit : s) {
			auto item = decode(bit);
			if (!item.cell || !editable(item.cell) || (state_q.size() && item.signal != state_q) || !values.insert(item.value).second) return;
			state_q = item.signal;
			selects.push_back(item);
			old_cells.insert(item.cell);
		}
		if (count != (1 << GetSize(state_q))) return;
		auto state = driver(state_q[0]);
		if (!ff_type(state) || !editable(state, ID::Q)) return;
		FfData ff(&initvals, state);
		if (!ff.has_clk || ff.has_ce || ff.has_arst || ff.has_srst || ff.has_sr || ff.has_aload || sigmap(ff.sig_q) != state_q || !ff.val_init.is_fully_def()) return;
		old_cells.insert(state);
		auto select_d = sigmap(ff.sig_d);
		pool<Cell *> banks;
		SigSpec new_b, new_s;
		Const output_init;
		for (int i = 0; i < count; i++) {
			auto q = b.extract(i * width, width);
			auto bank = driver(q[0]);
			if (!ff_type(bank) || !editable(bank, ID::Q) || !banks.insert(bank).second || bank == state) return;
			FfData data(&initvals, bank);
			if (!data.has_clk || data.has_arst || data.has_srst || data.has_sr || data.has_aload || data.pol_clk != ff.pol_clk || sigmap(data.sig_clk) != sigmap(ff.sig_clk) || sigmap(data.sig_q) != q) return;
			SigSpec input = sigmap(data.sig_d), enable;
			Cell *feedback = nullptr;
			if (data.has_ce) {
				if (!data.pol_ce) return;
				enable = sigmap(data.sig_ce);
			} else {
				feedback = driver(input[0]);
				if (!editable(feedback) || feedback->type != ID($mux) || sigmap(feedback->getPort(ID::Y)) != input || sigmap(feedback->getPort(ID::A)) != q) return;
				enable = sigmap(feedback->getPort(ID::S));
				input = sigmap(feedback->getPort(ID::B));
				old_cells.insert(feedback);
			}
			if (GetSize(enable) != 1) return;
			auto capture = decode(enable[0]);
			if (!capture.cell || capture.signal != select_d || capture.value != selects[i].value) return;
			old_cells.insert(bank);
			new_b.append(input);
			new_s.append(enable);
			if (selects[i].value == ff.val_init.as_int()) output_init = data.val_init;
		}
		if (GetSize(output_init) != width || !output_init.is_fully_def()) return;
		if (!private_to(state_q, old_cells)) return;
		for (auto item : selects) if (!private_to(sigmap(item.cell->getPort(ID::Y)), old_cells)) return;
		for (auto bank : banks) if (!private_to(sigmap(bank->getPort(ID::Q)), old_cells)) return;
		for (auto item : old_cells) if (item != cell && item != state && !banks.count(item) && item->type == ID($mux))
			if (!private_to(sigmap(item->getPort(ID::Y)), old_cells)) return;
		for (auto signal : {new_b, new_s, sigmap(ff.sig_clk)}) for (auto bit : signal)
			if (old_cells.count(driver(bit))) return;
		// 关系 y=M(sr,bank) 在初始条件成立；每个时钟边沿所选 bank 捕获对应输入，因此关系经一步保持。
		auto input = module->addWire(NEW_ID, width);
		module->addPmux(NEW_ID, cell->getPort(ID::A), new_b, new_s, input);
		FfData output(module, &initvals, NEW_ID);
		output.has_clk = true;
		output.pol_clk = ff.pol_clk;
		output.sig_clk = ff.sig_clk;
		output.width = width;
		output.sig_q = cell->getPort(ID::Y);
		output.sig_d = input;
		output.val_init = output_init;
		output.emit();
		for (auto old : old_cells) {
			if (ff_type(old)) initvals.remove_init(sigmap(old->getPort(ID::Q)));
			removed.insert(old);
		}
	}

	void run()
	{
		auto cells = module->selected_cells();
		for (auto cell : cells) if (cell->type == ID($pmux) && budget > 0) compress(cell);
		for (auto cell : cells) if (!removed.count(cell) && budget > 0) decode_onehot(cell);
		for (auto cell : cells) if (!removed.count(cell) && budget > 0) specialize(cell);
		for (auto cell : removed) module->remove(cell);
	}
};

struct OptPmuxStatePass : Pass {
	OptPmuxStatePass() : Pass("opt_pmuxstate", "specialize PMUX data and prove observable state reductions") {}
	void help() override
	{
		log("    opt_pmuxstate [selection]\n\n");
		log("Propagate branch-local comparison facts into mux data.\n");
		log("Replace onehot equality decodes after proving initialization and permutation transitions.\n");
		log("Compress private, initialized, synchronously captured banks with complete binary selection.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			bool candidate = false;
			for (auto cell : module->selected_cells()) if (cell->type == ID($pmux)) {
				candidate = true;
				break;
			}
			if (candidate) PmuxStateWorker(module, design).run();
		}
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END
