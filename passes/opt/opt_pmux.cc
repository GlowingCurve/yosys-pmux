#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptPmuxWorker
{
	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell*> driver;
	dict<std::pair<SigSpec, SigSpec>, SigBit> mux_cache;
	int replaced_bits = 0;
	int lut_count = 0;

	OptPmuxWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				for (auto bit : sigmap(conn.second))
					driver[bit] = cell;

		// collect first, optimize() removes cells
		vector<Cell*> pmux_cells;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				pmux_cells.push_back(cell);

		for (auto cell : pmux_cells)
			optimize(cell);
	}

	// decompose a select bit into "base == value"
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

	// inputs[0] is dataa, the LSB of the lut_mask index
	SigBit add_lut(const Const &mask, vector<SigBit> inputs)
	{
		log_assert(GetSize(inputs) <= 4);
		while (GetSize(inputs) < 4)
			inputs.push_back(State::S1);

		Cell *cell = module->addCell(NEW_ID, ID(cycloneive_lcell_comb));
		cell->setParam(ID(lut_mask), mask);
		cell->setParam(ID(sum_lutc_input), Const("datac"));
		cell->setPort(ID(dataa), inputs[0]);
		cell->setPort(ID(datab), inputs[1]);
		cell->setPort(ID(datac), inputs[2]);
		cell->setPort(ID(datad), inputs[3]);

		Wire *y = module->addWire(NEW_ID);
		cell->setPort(ID(combout), y);
		lut_count++;
		return y;
	}

	// return d[k] where k is the value of s (LSB first), GetSize(d) == 2^GetSize(s)
	SigBit build_mux(const vector<SigBit> &d, const SigSpec &s)
	{
		auto key = std::make_pair(SigSpec(d), s);
		auto it = mux_cache.find(key);
		if (it != mux_cache.end())
			return it->second;

		SigBit y = build_mux_uncached(d, s);
		mux_cache[key] = y;
		return y;
	}

	SigBit build_mux_uncached(const vector<SigBit> &d, const SigSpec &s)
	{
		bool all_equal = true;
		for (auto bit : d)
			if (bit != d[0])
				all_equal = false;
		if (all_equal)
			return d[0];

		// drop select bits the data does not depend on
		for (int i = 0; i < GetSize(s); i++) {
			bool independent = true;
			for (int k = 0; k < GetSize(d); k++)
				if (!(k & (1 << i)) && d[k] != d[k | (1 << i)])
					independent = false;
			if (!independent)
				continue;

			vector<SigBit> new_d;
			for (int k = 0; k < GetSize(d); k++)
				if (!(k & (1 << i)))
					new_d.push_back(d[k]);
			SigSpec new_s = s;
			new_s.remove(i);
			return build_mux(new_d, new_s);
		}

		// one LUT is enough if the distinct data signals and the select bits fit into 4 inputs
		idict<SigBit> data_idx;
		for (auto bit : d)
			data_idx(bit);
		if (GetSize(data_idx) + GetSize(s) <= 4) {
			vector<SigBit> inputs;
			for (auto bit : data_idx)
				inputs.push_back(bit);
			int sel_offset = GetSize(inputs);
			for (auto bit : s)
				inputs.push_back(bit);

			// unused inputs are tied to 1, so fill all 16 rows of the mask
			vector<State> mask(16);
			for (int row = 0; row < 16; row++) {
				int k = 0;
				for (int i = 0; i < GetSize(s); i++)
					if (row & (1 << (sel_offset + i)))
						k |= 1 << i;
				mask[row] = (row & (1 << data_idx.at(d[k]))) ? State::S1 : State::S0;
			}
			return add_lut(Const(mask), inputs);
		}

		if (GetSize(s) == 2) {
			// t = s0 ? s1 : (s1 ? d2 : d0), y = s0 ? (t ? d3 : d1) : t
			SigBit t = add_lut(Const(0xf0ca, 16), {d[0], d[2], s[1], s[0]});
			return add_lut(Const(0xcaf0, 16), {d[1], d[3], t, s[0]});
		}

		// split on the two lowest select bits, then select among the groups
		vector<SigBit> groups;
		for (int k = 0; k < GetSize(d); k += 4)
			groups.push_back(build_mux({d[k], d[k+1], d[k+2], d[k+3]}, s.extract(0, 2)));
		return build_mux(groups, s.extract(2, GetSize(s) - 2));
	}

	void optimize(Cell *cell)
	{
		int width = cell->getParam(ID::WIDTH).as_int();
		SigSpec sig_a = cell->getPort(ID::A);
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		SigSpec sig_s = cell->getPort(ID::S);
		SigSpec sig_y = cell->getPort(ID::Y);

		// all select bits must compare the same base signal against constants
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

		// the values must be distinct and cover 0 .. 2^n-1
		vector<int> index(1 << n, -1);
		for (int i = 0; i < GetSize(values); i++) {
			if (values[i] < 0 || values[i] >= (1 << n) || index[values[i]] != -1)
				return;
			index[values[i]] = i;
		}
		for (int v = 0; v < (1 << n); v++)
			if (index[v] == -1)
				return;

		// output bits whose data are all signals become LUT trees, the rest stay in a narrower $pmux
		int old_lut_count = lut_count;
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

		log("  %s: replaced %d of %d bits with %d LUTs, select = %s\n", log_id(cell), GetSize(new_bits), width,
				lut_count - old_lut_count, log_signal(base));
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

		module->remove(cell);
		for (auto &it : new_bits)
			module->connect(sig_y[it.first], it.second);
	}
};

struct OptPmuxPass : public Pass {
	OptPmuxPass() : Pass("opt_pmux", "replace fully decoded $pmux cells with LUT trees") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_pmux [selection]\n");
		log("\n");
		log("This pass replaces $pmux cells whose select bits are $eq/$logic_not cells\n");
		log("comparing the same signal against all of its values. Each output bit is\n");
		log("rebuilt as a tree of cycloneive_lcell_comb cells selected directly by that\n");
		log("signal. Identical data inputs are merged and select bits the data does not\n");
		log("depend on are dropped.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_PMUX pass (replace fully decoded $pmux cells).\n");
		extra_args(args, 1, design);

		int replaced_bits = 0, lut_count = 0;
		for (auto module : design->selected_modules()) {
			OptPmuxWorker worker(module);
			replaced_bits += worker.replaced_bits;
			lut_count += worker.lut_count;
		}

		log("Replaced %d $pmux output bits with %d LUTs.\n", replaced_bits, lut_count);
	}
} OptPmuxPass;

PRIVATE_NAMESPACE_END
