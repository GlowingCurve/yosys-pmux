// opt_pmuxstate 根据分支条件传播常量，压缩同步捕获寄存器组，并化简独热状态比较。
#include "kernel/yosys.h"
#include "kernel/ff.h"
#include "passes/opt/pmux_decoder.h"
#include "passes/opt/pmux_netlist.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxStateWorker {
	Module *module;
	PmuxNetlist netlist;
	PmuxDecoder decoder;
	FfInitVals initvals;
	pool<Cell *> onehot_states;
	int proved_states = 0, reused_states = 0, proved_muxes = 0, proved_permutations = 0;
	int compressed_groups = 0, compressed_cells = 0;
	int budget = 262144;

	PmuxStateWorker(Module *module, Design *design) :
		module(module), netlist(module, design), decoder(netlist), initvals(&netlist.sigmap(), module) {}

	bool spend(int amount)
	{
		budget -= amount;
		return budget >= 0;
	}

	void specialize(Cell *cell)
	{
		if (!cell->type.in(ID($mux), ID($pmux)) || !netlist.editable(cell)) return;
		const auto &s = netlist.port(cell, ID::S);
		auto a = cell->getPort(ID::A), b = cell->getPort(ID::B);
		int width = GetSize(a);
		if (width > 4096 || GetSize(s) > 16 || !spend(width * GetSize(s))) return;
		bool parallel = cell->type == ID($pmux);
		int branches = parallel ? GetSize(s) : 2;
		for (int index = 0; index < branches && budget > 0; index++) {
			bool selected = parallel || index != 0;
			IdString port = selected ? ID::B : ID::A;
			int offset = parallel ? index * width : 0;
			dict<SigBit, State> facts;
			if (!decoder.condition(s[parallel ? index : 0], selected, facts, budget)) continue;
			auto &signal = selected ? b : a;
			auto replacement = signal.extract(offset, width);
			const auto &mapped = netlist.port(cell, port);
			for (int i = 0; i < width; i++) {
				auto fact = facts.find(mapped[offset + i]);
				if (fact != facts.end()) replacement[i] = fact->second;
			}
			if (netlist.sigmap()(replacement).is_fully_def())
				signal.replace(offset, replacement);
		}
		bool changed_a = a != cell->getPort(ID::A), changed_b = b != cell->getPort(ID::B);
		if (!parallel && width == 1 && changed_a != changed_b) {
			auto input = netlist.port(cell, changed_a ? ID::A : ID::B)[0];
			auto other = netlist.port(cell, changed_a ? ID::B : ID::A)[0];
			// 单比特选择仍占用一个 LUT，保留继续被使用的数据输入。
			if (other.wire && (netlist.protected_bit(input) || GetSize(netlist.users(input)) > 1))
				return;
		}
		if (changed_a) netlist.set_port(cell, ID::A, a);
		if (changed_b) netlist.set_port(cell, ID::B, b);
	}

	bool onehot(const Const &value)
	{
		if (!value.is_fully_def()) return false;
		int count = 0;
		for (auto bit : value) count += bit == State::S1;
		return count == 1;
	}

	bool ff_type(IdString type)
	{
		return type.in(ID($dff), ID($dffe), ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce));
	}

	bool permutation(const SigSpec &d, const SigSpec &q)
	{
		if (GetSize(d) != GetSize(q)) return false;
		pool<SigBit> expected(q.begin(), q.end()), actual(d.begin(), d.end());
		return GetSize(expected) == GetSize(q) && actual == expected;
	}

	struct OnehotUpdate {
		pool<Cell *> active, muxes;
		dict<SigSpec, int> heights;
		pool<SigSpec> permutations;
	};

	bool onehot_update(SigSpec value, const SigSpec &q, OnehotUpdate &proof, int &height, int depth = 0)
	{
		if (depth > 8 || GetSize(value) != GetSize(q) || !spend(GetSize(value))) return false;
		value = netlist.sigmap()(value);
		auto found = proof.heights.find(value);
		if (found != proof.heights.end()) {
			height = found->second;
			return depth + height <= 8;
		}
		if (permutation(value, q)) {
			proof.permutations.insert(value);
			proof.heights[value] = 0;
			height = 0;
			return true;
		}
		if (value.is_fully_def() && onehot(value.as_const())) {
			proof.heights[value] = 0;
			height = 0;
			return true;
		}
		auto cell = netlist.driver(value[0]);
		if (!cell || cell->type != ID($mux) || !netlist.editable(cell) || netlist.port(cell, ID::Y) != value) return false;
		if (GetSize(cell->getPort(ID::A)) != GetSize(q) || GetSize(cell->getPort(ID::B)) != GetSize(q) ||
			GetSize(cell->getPort(ID::S)) != 1) return false;
		if (proof.active.count(cell) || (!proof.muxes.count(cell) && GetSize(proof.muxes) >= 16)) return false;
		if (!spend(2 * GetSize(q) + 1)) return false;
		proof.active.insert(cell);
		proof.muxes.insert(cell);
		int a_height = 0, b_height = 0;
		bool valid = onehot_update(cell->getPort(ID::A), q, proof, a_height, depth + 1) &&
			onehot_update(cell->getPort(ID::B), q, proof, b_height, depth + 1);
		proof.active.erase(cell);
		if (!valid) return false;
		height = 1 + std::max(a_height, b_height);
		log_assert(depth + height <= 8);
		proof.heights[value] = height;
		return true;
	}

	bool prove_onehot_state(Cell *state)
	{
		if (onehot_states.count(state)) {
			reused_states++;
			return true;
		}
		log_assert(ff_type(state->type));
		if (!netlist.editable(state, ID::Q)) return false;
		FfData ff(&initvals, state);
		auto q = netlist.sigmap()(ff.sig_q);
		int width = GetSize(q);
		if (!ff.has_clk || ff.has_aload || ff.has_sr || width < 2 || width > 64 || !spend(width)) return false;
		pool<SigBit> unique(q.begin(), q.end());
		if (GetSize(unique) != width || GetSize(ff.val_init) != width || !onehot(ff.val_init)) return false;
		if (ff.has_arst && (GetSize(ff.val_arst) != width || !onehot(ff.val_arst))) return false;
		if (ff.has_srst && (GetSize(ff.val_srst) != width || !onehot(ff.val_srst))) return false;
		OnehotUpdate proof;
		int height = 0;
		if (!onehot_update(ff.sig_d, q, proof, height)) return false;
		onehot_states.insert(state);
		proved_states++;
		proved_muxes += GetSize(proof.muxes);
		proved_permutations += GetSize(proof.permutations);
		return true;
	}

	struct OnehotDecode {
		Cell *cell;
		SigBit replacement;
	};

	void collect_onehot_decode(Cell *cell, std::vector<OnehotDecode> &replacements)
	{
		if (!cell->type.in(ID($eq), ID($logic_not)) || GetSize(cell->getPort(ID::Y)) != 1 || !netlist.editable(cell)) return;
		PmuxDecoder::Cube cube;
		if (!decoder.decode(netlist.port(cell, ID::Y)[0], cube) || cube.dead) return;
		int width = GetSize(cube.bits);
		if (width < 2 || width > 64 || !spend(width)) return;
		log_assert(cube.cell == cell);
		auto state = netlist.driver(cube.bits.begin()->first);
		if (!state || !ff_type(state->type)) return;
		const auto &q = netlist.port(state, ID::Q);
		if (GetSize(q) != width) return;
		SigBit selected;
		for (auto bit : q) {
			auto binding = cube.bits.find(bit);
			if (binding == cube.bits.end()) return;
			if (!binding->second) continue;
			if (selected.wire) return;
			selected = bit;
		}
		if (selected.wire && prove_onehot_state(state))
			replacements.push_back({cell, selected});
	}

	void rewrite_onehot_decodes()
	{
		std::vector<OnehotDecode> replacements;
		for (auto cell : module->selected_cells()) {
			if (budget <= 0) break;
			collect_onehot_decode(cell, replacements);
		}
		for (const auto &item : replacements) {
			log_assert(netlist.editable(item.cell));
			auto output = item.cell->getPort(ID::Y);
			netlist.forget_cell(item.cell);
			module->remove(item.cell);
			netlist.connect(output, item.replacement);
		}
		if (!replacements.empty())
			log("opt_pmuxstate %s: onehot_states=%d reuses=%d update_muxes=%d permutations=%d decodes=%d.\n",
				log_id(module), proved_states, reused_states, proved_muxes, proved_permutations, GetSize(replacements));
	}

	bool capture_matches(SigBit enable, const PmuxDecoder::Cube &select, const SigSpec &q, const SigSpec &d) const
	{
		PmuxDecoder::Cube capture;
		if (!decoder.decode(enable, capture) || !capture.cell) return false;
		log_assert(GetSize(q) == GetSize(d));
		dict<SigBit, bool> expected;
		bool dead = false;
		for (int i = 0; i < GetSize(q); i++) {
			bool value = select.bits.at(q[i]);
			auto bit = d[i];
			if (!bit.wire) {
				if (bit != State::S0 && bit != State::S1) return false;
				dead |= (bit == State::S1) != value;
			} else {
				auto binding = expected.emplace(bit, value);
				dead |= !binding.second && binding.first->second != value;
			}
		}
		return capture.dead == dead && (dead || capture.bits == expected);
	}

	void compress(Cell *cell)
	{
		if (!netlist.editable(cell)) return;
		const auto &b = netlist.port(cell, ID::B);
		int count = GetSize(netlist.port(cell, ID::S)), width = GetSize(netlist.port(cell, ID::A));
		if (count < 2 || count > 16 || width > 4096 || !netlist.port(cell, ID::A).is_fully_undef() || !spend(count * width)) return;
		log_assert(width > 0);
		PmuxDecoder::Table table;
		if (!decoder.table(cell, table) || !table.prefix.empty() || count != GetSize(table.branch_for_code)) return;
		auto state = netlist.driver(table.control[0]);
		if (!state || !ff_type(state->type) || !netlist.editable(state, ID::Q)) return;
		FfData ff(&initvals, state);
		const auto &state_q = netlist.port(state, ID::Q);
		if (!ff.has_clk || ff.has_ce || ff.has_arst || ff.has_srst || ff.has_sr || ff.has_aload ||
			GetSize(state_q) != GetSize(table.control) || !ff.val_init.is_fully_def()) return;
		dict<SigBit, int> offsets;
		for (int i = 0; i < GetSize(state_q); i++) offsets.emplace(state_q[i], i);
		int initial_code = 0;
		for (int i = 0; i < GetSize(table.control); i++) {
			auto offset = offsets.find(table.control[i]);
			if (offset == offsets.end()) return;
			if (ff.val_init[offset->second] == State::S1)
				initial_code |= 1 << i;
		}
		int initial_branch = table.branch_for_code[initial_code];
		log_assert(initial_branch >= 0 && initial_branch < count);
		auto old_cells = table.region;
		old_cells.insert(state);
		auto select_d = netlist.sigmap()(ff.sig_d);
		auto clock = netlist.sigmap()(ff.sig_clk);
		pool<Cell *> banks;
		SigSpec new_b, new_s;
		Const output_init;
		for (int i = 0; i < count; i++) {
			auto q = b.extract(i * width, width);
			auto bank = netlist.driver(q[0]);
			if (!bank || !ff_type(bank->type) || !netlist.editable(bank, ID::Q) || !banks.insert(bank).second || bank == state) return;
			FfData data(&initvals, bank);
			if (!data.has_clk || data.has_arst || data.has_srst || data.has_sr || data.has_aload || data.pol_clk != ff.pol_clk ||
				netlist.sigmap()(data.sig_clk) != clock || netlist.port(bank, ID::Q) != q) return;
			SigSpec input = netlist.sigmap()(data.sig_d), enable;
			if (data.has_ce) {
				if (!data.pol_ce) return;
				enable = netlist.sigmap()(data.sig_ce);
			} else {
				auto feedback = netlist.driver(input[0]);
				if (!feedback || feedback->type != ID($mux) || !netlist.editable(feedback) ||
					netlist.port(feedback, ID::Y) != input || netlist.port(feedback, ID::A) != q) return;
				enable = netlist.port(feedback, ID::S);
				input = netlist.port(feedback, ID::B);
				old_cells.insert(feedback);
			}
			if (GetSize(enable) != 1 || !capture_matches(enable[0], table.cubes[i], state_q, select_d)) return;
			old_cells.insert(bank);
			new_b.append(input);
			new_s.append(enable);
			if (i == initial_branch) output_init = data.val_init;
		}
		if (GetSize(output_init) != width || !output_init.is_fully_def()) return;
		pool<SigBit> retained;
		for (const auto *signal : {&new_b, &new_s, &clock})
			retained.insert(signal->begin(), signal->end());
		const auto &y = netlist.port(cell, ID::Y);
		pool<SigBit> targets(y.begin(), y.end());
		auto removed = netlist.private_cells(old_cells, {cell}, targets, retained);
		if (removed != old_cells) return;
		if (!spend(2 * width + GetSize(new_b) + GetSize(new_s) + 1)) return;
		// 关系 y=M(sr,bank) 在初始条件成立；每个时钟边沿所选 bank 捕获对应输入，因此关系经一步保持。
		auto input = module->addWire(NEW_ID, width);
		auto shared_mux = module->addPmux(NEW_ID, cell->getPort(ID::A), new_b, new_s, input);
		FfData output(module, &initvals, NEW_ID);
		output.has_clk = true;
		output.pol_clk = ff.pol_clk;
		output.sig_clk = ff.sig_clk;
		output.width = width;
		output.sig_q = cell->getPort(ID::Y);
		output.sig_d = input;
		output.val_init = output_init;
		auto shared_ff = output.emit();
		log_assert(shared_ff);
		for (auto old : removed) {
			if (ff_type(old->type)) initvals.remove_init(netlist.port(old, ID::Q));
			netlist.forget_cell(old);
			module->remove(old);
		}
		netlist.register_cell(shared_mux);
		netlist.register_cell(shared_ff);
		compressed_groups++;
		compressed_cells += GetSize(removed);
	}

	void compress_banks()
	{
		std::vector<Cell *> candidates;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				candidates.push_back(cell);
		for (auto cell : candidates) {
			if (budget <= 0) break;
			compress(cell);
		}
		if (compressed_groups != 0)
			log("opt_pmuxstate %s: compressed_bank_groups=%d removed_cells=%d.\n", log_id(module), compressed_groups, compressed_cells);
	}

	void specialize_branches()
	{
		for (auto cell : module->selected_cells()) {
			if (budget <= 0) break;
			specialize(cell);
		}
	}
};

struct OptPmuxStatePass : Pass {
	OptPmuxStatePass() : Pass("opt_pmuxstate", "specialize PMUX data and prove observable state reductions") {}
	void help() override
	{
		log("    opt_pmuxstate [selection]\n\n");
		log("Propagate branch-local comparison facts into mux data.\n");
		log("Replace onehot equality decodes after proving initialized bounded mux updates.\n");
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
			if (!candidate) continue;
			PmuxStateWorker worker(module, design);
			worker.compress_banks();
			worker.rewrite_onehot_decodes();
			worker.specialize_branches();
		}
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END
