#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// a hash-consed DAG of word-level 2:1 muxes, id -1 is an all-x word
struct MuxDag
{
	struct Node {
		SigSpec leaf;
		SigBit sel;
		int lo = -1, hi = -1;
	};

	vector<Node> nodes;
	dict<SigSpec, int> leaf_cache;
	dict<std::tuple<SigBit, int, int>, int> mux_cache;
	int mux_count = 0;

	int leaf(const SigSpec &sig)
	{
		if (sig.is_fully_undef())
			return -1;
		auto it = leaf_cache.find(sig);
		if (it != leaf_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().leaf = sig;
		return leaf_cache[sig] = GetSize(nodes) - 1;
	}

	// sel ? hi : lo, an all-x side is a don't care
	int mux(SigBit sel, int lo, int hi)
	{
		if (lo == hi || hi == -1)
			return lo;
		if (lo == -1)
			return hi;
		auto key = std::make_tuple(sel, lo, hi);
		auto it = mux_cache.find(key);
		if (it != mux_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().sel = sel;
		nodes.back().lo = lo;
		nodes.back().hi = hi;
		mux_count++;
		return mux_cache[key] = GetSize(nodes) - 1;
	}

	// return d[k] where k is the value of s (LSB first), GetSize(d) == 2^GetSize(s)
	int tree(vector<int> d, const SigSpec &s)
	{
		for (auto sel : s) {
			vector<int> next;
			for (int k = 0; k < GetSize(d); k += 2)
				next.push_back(mux(sel, d[k], d[k+1]));
			d.swap(next);
		}
		log_assert(GetSize(d) == 1);
		return d[0];
	}

	// children are always created before their parents
	vector<SigSpec> emit(Module *module, int width)
	{
		vector<SigSpec> sig(GetSize(nodes));
		auto get = [&](int id) { return id == -1 ? SigSpec(State::Sx, width) : sig[id]; };
		for (int id = 0; id < GetSize(nodes); id++) {
			const Node &n = nodes[id];
			if (n.lo == -1 && n.hi == -1) {
				sig[id] = n.leaf;
				continue;
			}
			sig[id] = module->addWire(NEW_ID, width);
			module->addMux(NEW_ID, get(n.lo), get(n.hi), n.sel, sig[id]);
		}
		return sig;
	}
};

// a $pmux whose select bits are "base == value", tabulated over all values of base
struct PmuxTable
{
	Cell *cell;
	SigSpec base;
	vector<SigSpec> data;
};

struct MuxtreeShareWorker
{
	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell*> driver;
	int shared_pairs = 0;
	int saved_muxes = 0;

	MuxtreeShareWorker(Module *module) : module(module)
	{
		dict<std::pair<SigSpec, int>, vector<PmuxTable>> groups;
		update_index();
		for (auto cell : module->selected_cells()) {
			PmuxTable t;
			if (cell->type == ID($pmux) && decode(cell, t))
				groups[std::make_pair(t.base, cell->getParam(ID::WIDTH).as_int())].push_back(t);
		}

		for (auto &it : groups)
			if (GetSize(it.second) >= 2)
				share_group(it.second);
	}

	void update_index()
	{
		sigmap.set(module);
		driver.clear();
		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				for (auto bit : sigmap(conn.second))
					driver[bit] = cell;
	}
	// decompose a select bit into "base == value", value == -1 if the compare is never true
	bool match_select(SigBit s, SigSpec &base, int &value)
	{
		auto it = driver.find(sigmap(s));
		if (it == driver.end())
			return false;

		Cell *cmp = it->second;
		if (!cmp->type.in(ID($eq), ID($logic_not)) || sigmap(cmp->getPort(ID::Y)[0]) != sigmap(s))
			return false;

		SigSpec a = sigmap(cmp->getPort(ID::A));
		SigSpec b;
		if (cmp->type == ID($logic_not)) {
			b = Const(0, GetSize(a));
		} else if (cmp->type == ID($eq)) {
			b = sigmap(cmp->getPort(ID::B));
			if (a.is_fully_const())
				std::swap(a, b);
			if (!b.is_fully_def())
				return false;
			bool is_signed = cmp->getParam(ID::A_SIGNED).as_bool() && cmp->getParam(ID::B_SIGNED).as_bool();
			if (is_signed && GetSize(a) != GetSize(b))
				return false;
		} else
			return false;

		if (GetSize(a) == 0 || GetSize(a) > 8)
			return false;

		// "a == b" with b zero-extended to the width of a, or the other way around
		value = 0;
		for (int i = 0; i < GetSize(b); i++) {
			if (b[i] != State::S1)
				continue;
			if (i >= GetSize(a)) {
				value = -1;
				break;
			}
			value |= 1 << i;
		}
		base = a;
		return true;
	}

	bool decode(Cell *cell, PmuxTable &t)
	{
		int width = cell->getParam(ID::WIDTH).as_int();
		SigSpec sig_a = sigmap(cell->getPort(ID::A));
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		SigSpec sig_s = sigmap(cell->getPort(ID::S));

		vector<int> values;
		for (auto s : sig_s) {
			SigSpec this_base;
			int value;
			if (!match_select(s, this_base, value))
				return false;
			if (t.base.empty())
				t.base = this_base;
			else if (this_base != t.base)
				return false;
			values.push_back(value);
		}
		if (t.base.empty())
			return false;

		// values not matched by any select bit take A, two bits with the same value would be active at once
		t.cell = cell;
		t.data.assign(1 << GetSize(t.base), sig_a);
		pool<int> seen;
		for (int i = 0; i < GetSize(values); i++) {
			if (values[i] < 0)
				continue;
			if (seen.count(values[i]))
				return false;
			seen.insert(values[i]);
			t.data[values[i]] = sig_b.extract(i * width, width);
		}
		return true;
	}

	// the plain mux trees of p and q, built in one DAG so identical subtrees are counted once
	int plain_cost(const PmuxTable &p, const PmuxTable &q)
	{
		MuxDag dag;
		vector<int> dp, dq;
		for (auto &sig : p.data)
			dp.push_back(dag.leaf(sig));
		for (auto &sig : q.data)
			dq.push_back(dag.leaf(sig));
		dag.tree(dp, p.base);
		dag.tree(dq, q.base);
		return dag.mux_count;
	}

	// q(v) == p(v ^ 2^j) for most v: select the common words with the other bits, then swap on bit j
	std::pair<int, int> share(MuxDag &dag, const PmuxTable &p, const PmuxTable &q, int j)
	{
		int n = GetSize(p.base);
		SigBit sel_j = p.base[j];
		SigSpec sel_rest = p.base;
		sel_rest.remove(j);

		vector<int> leaf0, leaf1;
		for (int u = 0; u < (1 << (n - 1)); u++) {
			int low = u & ((1 << j) - 1);
			int v0 = ((u >> j) << (j + 1)) | low;
			int v1 = v0 | (1 << j);
			// t0 is p(v) when bit j is 0 and q(v) when it is 1, t1 the other way round
			leaf0.push_back(dag.mux(sel_j, dag.leaf(p.data[v0]), dag.leaf(q.data[v1])));
			leaf1.push_back(dag.mux(sel_j, dag.leaf(q.data[v0]), dag.leaf(p.data[v1])));
		}

		int t0 = dag.tree(leaf0, sel_rest);
		int t1 = dag.tree(leaf1, sel_rest);
		return std::make_pair(dag.mux(sel_j, t0, t1), dag.mux(sel_j, t1, t0));
	}

	// whether sig combinationally depends on any bit in target
	bool depends_on(const SigSpec &sig, const pool<SigBit> &target)
	{
		pool<SigBit> visited;
		vector<SigBit> queue;
		for (auto bit : sigmap(sig))
			if (bit.wire)
				queue.push_back(bit);

		while (!queue.empty()) {
			SigBit bit = queue.back();
			queue.pop_back();
			if (target.count(bit))
				return true;
			if (visited.count(bit))
				continue;
			visited.insert(bit);

			auto it = driver.find(bit);
			if (it == driver.end() || RTLIL::builtin_ff_cell_types().count(it->second->type))
				continue;
			for (auto &conn : it->second->connections())
				if (it->second->input(conn.first))
					for (auto in : sigmap(conn.second))
						if (in.wire)
							queue.push_back(in);
		}
		return false;
	}

	// sharing makes each output depend on the data of the other
	bool may_share(const PmuxTable &p, const PmuxTable &q)
	{
		pool<SigBit> p_y, q_y;
		for (auto bit : sigmap(p.cell->getPort(ID::Y)))
			p_y.insert(bit);
		for (auto bit : sigmap(q.cell->getPort(ID::Y)))
			q_y.insert(bit);

		SigSpec p_data, q_data;
		for (auto &sig : p.data)
			p_data.append(sig);
		for (auto &sig : q.data)
			q_data.append(sig);
		return !depends_on(p_data, q_y) && !depends_on(q_data, p_y);
	}

	void share_group(const vector<PmuxTable> &tables)
	{
		// (gain, p, q, j), larger gain first
		vector<std::tuple<int, int, int, int>> candidates;
		int n = GetSize(tables[0].base);
		for (int p = 0; p < GetSize(tables); p++)
		for (int q = p + 1; q < GetSize(tables); q++) {
			int plain = plain_cost(tables[p], tables[q]);
			for (int j = 0; j < n; j++) {
				MuxDag dag;
				share(dag, tables[p], tables[q], j);
				if (dag.mux_count < plain)
					candidates.push_back(std::make_tuple(plain - dag.mux_count, p, q, j));
			}
		}
		std::sort(candidates.begin(), candidates.end(), [](const std::tuple<int, int, int, int> &a, const std::tuple<int, int, int, int> &b) {
			if (std::get<0>(a) != std::get<0>(b))
				return std::get<0>(a) > std::get<0>(b);
			return std::make_tuple(std::get<1>(a), std::get<2>(a), std::get<3>(a)) < std::make_tuple(std::get<1>(b), std::get<2>(b), std::get<3>(b));
		});

		pool<int> used;
		for (auto &c : candidates) {
			int gain = std::get<0>(c), p = std::get<1>(c), q = std::get<2>(c), j = std::get<3>(c);
			if (used.count(p) || used.count(q) || !may_share(tables[p], tables[q]))
				continue;
			used.insert(p);
			used.insert(q);
			log("  %s and %s: shared on %s, %d fewer word muxes\n", log_id(tables[p].cell), log_id(tables[q].cell),
					log_signal(tables[p].base[j]), gain);
			apply(tables[p], tables[q], j);
			shared_pairs++;
			saved_muxes += gain;
			update_index();
		}
	}

	void apply(const PmuxTable &p, const PmuxTable &q, int j)
	{
		int width = p.cell->getParam(ID::WIDTH).as_int();
		MuxDag dag;
		auto roots = share(dag, p, q, j);
		vector<SigSpec> sig = dag.emit(module, width);

		SigSpec p_y = p.cell->getPort(ID::Y);
		SigSpec q_y = q.cell->getPort(ID::Y);
		module->remove(p.cell);
		module->remove(q.cell);
		module->connect(p_y, roots.first == -1 ? SigSpec(State::Sx, width) : sig[roots.first]);
		module->connect(q_y, roots.second == -1 ? SigSpec(State::Sx, width) : sig[roots.second]);
	}
};

struct MuxtreeSharePass : public Pass {
	MuxtreeSharePass() : Pass("muxtree_share", "share the select trees of $pmux pairs that differ in one select bit") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    muxtree_share [selection]\n");
		log("\n");
		log("This pass looks for pairs of $pmux cells whose select bits are $eq/$logic_not\n");
		log("cells comparing the same signal 'base' against constants, and where the second\n");
		log("$pmux mostly selects the data the first one selects with bit 'base[j]' inverted.\n");
		log("Both cells are then rebuilt as two mux trees over the other bits of 'base',\n");
		log("shared by both outputs and swapped by 'base[j]' at the root. Values where the\n");
		log("two cells disagree get an extra mux on 'base[j]' at the leaves. A pair is only\n");
		log("rebuilt if this needs fewer word-level $mux cells than two separate trees.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MUXTREE_SHARE pass (share select trees of $pmux pairs).\n");
		extra_args(args, 1, design);

		int shared_pairs = 0, saved_muxes = 0;
		for (auto module : design->selected_modules()) {
			MuxtreeShareWorker worker(module);
			shared_pairs += worker.shared_pairs;
			saved_muxes += worker.saved_muxes;
		}

		log("Shared %d $pmux pairs, %d fewer word-level muxes.\n", shared_pairs, saved_muxes);
	}
} MuxtreeSharePass;

PRIVATE_NAMESPACE_END
