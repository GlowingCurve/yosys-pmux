#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptPMUXWorker {
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> driver;
	int replaced_bits = 0;

	OptPMUXWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module), sigmap(module)
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						driver[bit] = cell;

		// 先收集再修改，避免遍历时删除 cell
		vector<Cell *> pmuxes;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				pmuxes.push_back(cell);
		for (auto cell : pmuxes)
			optimize(cell);
	}

	// 把选择位还原成 base == value
	bool match_select(SigBit s, SigSpec &base, int &value)
	{
		auto it = driver.find(sigmap(s));
		if (it == driver.end())
			return false;
		Cell *cmp = it->second;
		if (cmp->type == ID($logic_not)) {
			base = sigmap(cmp->getPort(ID::A));
			value = 0;
			return true;
		}
		if (cmp->type != ID($eq) || cmp->getParam(ID::A_SIGNED).as_bool())
			return false;
		SigSpec a = sigmap(cmp->getPort(ID::A));
		SigSpec b = sigmap(cmp->getPort(ID::B));
		if (a.is_fully_const())
			std::swap(a, b);
		if (!b.is_fully_const() || GetSize(b) > GetSize(a))
			return false;
		base = a;
		value = b.as_int();
		return true;
	}

	SigBit add_lut4(int mask, SigBit a, SigBit b, SigBit c, SigBit d)
	{
		Cell *lut = module->addCell(NEW_ID, ID(cycloneive_lcell_comb));
		lut->setParam(ID(lut_mask), Const(mask, 16));
		lut->setParam(ID(sum_lutc_input), Const("datac"));
		lut->setPort(ID(dataa), a);
		lut->setPort(ID(datab), b);
		lut->setPort(ID(datac), c);
		lut->setPort(ID(datad), d);
		Wire *y = module->addWire(NEW_ID);
		lut->setPort(ID(combout), y);
		return y;
	}

	// t = s0 ? s1 : (s1 ? d2 : d0)，y = s0 ? (t ? d3 : d1) : t
	SigBit mux4(SigBit d0, SigBit d1, SigBit d2, SigBit d3, SigBit s0, SigBit s1)
	{
		SigBit t = add_lut4(0xf0ca, d0, d2, s1, s0);
		return add_lut4(0xcaf0, d1, d3, t, s0);
	}

	// y = s ? b : a
	SigBit mux2(SigBit a, SigBit b, SigBit s) { return add_lut4(0xcaca, a, b, s, State::S1); }

	// d[k] 对应 s == k，s 低位在前
	SigBit build_mux(vector<SigBit> d, SigSpec s)
	{
		int i = 0;
		while (GetSize(d) > 1) {
			vector<SigBit> next;
			if (GetSize(s) - i >= 2) {
				for (int k = 0; k < GetSize(d); k += 4)
					next.push_back(mux4(d[k], d[k + 1], d[k + 2], d[k + 3], s[i], s[i + 1]));
				i += 2;
			} else {
				for (int k = 0; k < GetSize(d); k += 2)
					next.push_back(mux2(d[k], d[k + 1], s[i]));
				i += 1;
			}
			d = next;
		}
		return d[0];
	}

	void optimize(Cell *pmux)
	{
		int width = pmux->getParam(ID::WIDTH).as_int();
		SigSpec sig_a = pmux->getPort(ID::A);
		SigSpec sig_b = pmux->getPort(ID::B);
		SigSpec sig_s = pmux->getPort(ID::S);
		SigSpec sig_y = pmux->getPort(ID::Y);

		// 所有选择位必须是同一个 base 的等值比较
		SigSpec base;
		vector<int> values;
		for (auto s : sig_s) {
			SigSpec this_base;
			int value;
			if (!match_select(s, this_base, value))
				return;
			if (base.empty())
				base = this_base;
			else if (this_base != base)
				return;
			values.push_back(value);
		}
		int n = GetSize(base);
		if (n == 0 || n > 16 || base.has_const())
			return;

		// 取值必须互不相同，并且覆盖 0 .. 2^n-1
		vector<int> index(1 << n, -1);
		for (int i = 0; i < GetSize(values); i++) {
			if (values[i] >= (1 << n) || index[values[i]] != -1)
				return;
			index[values[i]] = i;
		}
		for (int v = 0; v < (1 << n); v++)
			if (index[v] == -1)
				return;

		// 逐位决定：数据全是信号的位换成 LUT 树，其余位留在缩窄后的 $pmux 里
		vector<int> keep_bits;
		vector<std::pair<int, SigBit>> new_bits;
		for (int j = 0; j < width; j++) {
			vector<SigBit> d;
			bool all_signal = true;
			for (int v = 0; v < (1 << n); v++) {
				SigBit bit = sig_b[index[v] * width + j];
				if (bit.wire == nullptr)
					all_signal = false;
				d.push_back(bit);
			}
			if (all_signal)
				new_bits.push_back({j, build_mux(d, base)});
			else
				keep_bits.push_back(j);
		}
		if (new_bits.empty())
			return;

		log("  %s: replaced %d of %d bits, select = %s\n", log_id(pmux), GetSize(new_bits), width, log_signal(base));
		replaced_bits += GetSize(new_bits);
		if (!keep_bits.empty()) {
			SigSpec new_a, new_b, new_y;
			for (int j : keep_bits) {
				new_a.append(sig_a[j]);
				new_y.append(sig_y[j]);
			}
			for (int i = 0; i < GetSize(sig_s); i++)
				for (int j : keep_bits)
					new_b.append(sig_b[i * width + j]);
			module->addPmux(NEW_ID, new_a, new_b, sig_s, new_y);
		}
		module->remove(pmux);
		for (auto &it : new_bits)
			module->connect(sig_y[it.first], it.second);
	}
};

struct OptPmuxGuidePass : public Pass {
	OptPmuxGuidePass() : Pass("opt_pmux", "replace fully decoded pmux with LUT trees") {}
	void execute(vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_PMUXOPT pass.\n");
		extra_args(args, 1, design);
		int total = 0;
		for (auto module : design->selected_modules()) {
			OptPMUXWorker worker(design, module);
			total += worker.replaced_bits;
		}
		log("Replaced %d pmux output bits.\n", total);
	}
} OptPmuxGuidePass;

PRIVATE_NAMESPACE_END
