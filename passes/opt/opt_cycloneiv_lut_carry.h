struct LutCarryOptions {
	int64_t max_cuts = -1, max_pairs = -1, max_work = -1, max_memory = -1, max_proof = -1;
	bool explicit_limits = false;
	bool parse(const std::vector<std::string> &args, size_t &position)
	{
		int64_t *target = nullptr;
		if (args[position] == "-max-cuts") target = &max_cuts;
		if (args[position] == "-max-pairs") target = &max_pairs;
		if (args[position] == "-max-work") target = &max_work;
		if (args[position] == "-max-memory") target = &max_memory;
		if (args[position] == "-max-proof") target = &max_proof;
		if (!target) return false;
		if (++position == args.size() || args[position].empty() ||
			args[position].find_first_not_of("0123456789") != std::string::npos || args[position].size() > 18)
			log_cmd_error("LUT carry limits require a nonnegative integer.\n");
		*target = std::stoll(args[position]);
		explicit_limits = true;
		return true;
	}
};

struct LutCarryBudget {
	int64_t cuts = 0, pairs = 0, work = 0, proof = 0, memory = 0, peak_memory = 0;
	int64_t cuts_limit, pairs_limit, work_limit, proof_limit, memory_limit;
	int64_t search_work_limit = 0, search_memory_limit = 0;
	int64_t search_proof_limit = 0, base_work = 0, available_work = 0;
	bool stopped = false, searching = true, search_stopped = false;
	std::string reason, search_reason, phase_name;
	LutCarryBudget(const LutCarryOptions &options, int64_t scale)
	{
		auto limit = [&](int64_t value, int64_t factor, int64_t ceiling) {
			return value >= 0 ? value : std::min(ceiling, factor * std::max<int64_t>(1, scale));
		};
		cuts_limit = limit(options.max_cuts, 32, 200000);
		pairs_limit = limit(options.max_pairs, 128, 200000);
		work_limit = limit(options.max_work, 8192, 24000000);
		proof_limit = limit(options.max_proof, 2048, 4000000);
		memory_limit = options.max_memory >= 0 ? options.max_memory :
			std::min<int64_t>(96 * 1024 * 1024, 8 * 1024 * 1024 + 8192 * scale);
		if (!cuts_limit || !pairs_limit || !work_limit || !proof_limit || !memory_limit) stop("zero budget");
	}
	void stop(const char *why) { stopped = true; if (reason.empty()) reason = why; }
	bool search_done() const { return stopped || (searching && search_stopped); }
	void phase(const char *name, int fifths)
	{
		if (fifths == 1) {
			base_work = work; available_work = work_limit - work;
			search_proof_limit = proof + (proof_limit - proof) / 3 * 2;
		}
		searching = true; search_stopped = false; phase_name = name;
		search_work_limit = base_work + available_work / 5 * fifths;
		search_memory_limit = memory_limit / 8 * (fifths == 3 ? 7 : 6);
	}
	void finish_search() { searching = false; search_stopped = false; }
	bool search_charge(int64_t &used, int64_t limit, int64_t soft_limit, int64_t amount, const char *why)
	{
		if (search_done()) return false;
		if (searching && amount > soft_limit - used) {
			search_stopped = true;
			if (!search_reason.empty()) search_reason += "; ";
			search_reason += phase_name + ": " + why;
			return false;
		}
		return charge(used,limit,amount,why);
	}
	bool charge(int64_t &used, int64_t limit, int64_t amount, const char *why)
	{
		log_assert(amount >= 0);
		if (stopped) return false;
		if (amount > limit - used) { stop(why); return false; }
		used += amount;
		return true;
	}
	bool spend(int64_t amount) { return search_charge(work, work_limit, search_work_limit, amount, "work limit"); }
	bool prove(int64_t amount) {
		if (search_done()) return false;
		if (amount > work_limit - work || (searching && amount > search_work_limit - work)) return spend(amount);
		return search_charge(proof, proof_limit, search_proof_limit, amount, "truth proof limit") && spend(amount);
	}
	bool cut() { return search_charge(cuts, cuts_limit, cuts_limit, 1, "cut limit"); }
	bool pair() { return search_charge(pairs, pairs_limit, pairs_limit, 1, "pair limit"); }
	bool reserve(int64_t amount)
	{
		if (!search_charge(memory, memory_limit, search_memory_limit, amount, "memory limit")) return false;
		peak_memory = std::max(peak_memory, memory);
		return true;
	}
	void release(int64_t bytes) { log_assert(bytes >= 0 && bytes <= memory); memory -= bytes; }
};

struct LutCarryCut {
	std::vector<SigBit> leaves;
	std::set<IdString> nodes;
	uint8_t truth = 0;
	bool operator<(const LutCarryCut &other) const { return std::tie(leaves, truth, nodes) < std::tie(other.leaves, other.truth, other.nodes); }
};

struct LutCarryNode {
	SigBit output;
	std::vector<SigBit> inputs;
	uint16_t truth = 0;
	bool removable = false;
	int rank = -1;
};

struct LutCarryPair {
	IdString sum, carry;
	LutCarryCut sum_cut, carry_cut;
	SigBit a, b, cin;
	uint16_t mask = 0;
	int initial = -1;
};

struct LutCarryStep {
	int pair = -1, segment = 0, position = 0;
	CarryRole role;
	SigBit input, output;
	uint16_t mask = 0;
};

struct LutCarryPlan {
	std::vector<int> path;
	std::set<IdString> deleting;
	std::set<SigBit> outputs;
	std::vector<LutCarryStep> steps;
	int gain = 0;
};

struct LutCarryWorker {
	Design *design;
	Module *module;
	LutCarryBudget &budget;
	SigMap sigmap;
	CellTypes types;
	std::map<SigBit, std::map<IdString, int>> drivers, users;
	std::map<SigBit, int> input_counts;
	std::set<SigBit> observable, protected_bits;
	std::map<IdString, std::vector<SigBit>> cell_inputs, cell_outputs;
	std::map<IdString, LutCarryNode> nodes;
	std::map<IdString,Const> source_attributes;
	std::set<IdString> sequential_cells;
	std::map<IdString, std::vector<LutCarryCut>> cuts;
	std::vector<IdString> order;
	std::vector<LutCarryPair> pairs;
	std::map<SigBit, std::vector<int>> cin_pairs;
	std::set<IdString> invalidated;
	int64_t owned_memory = 0;
	int accepted = 0, deleted = 0, added = 0;
	uint64_t generation = 0;

	LutCarryWorker(Design *design, Module *module, LutCarryBudget &budget) :
		design(design), module(module), budget(budget), sigmap(module)
	{
		types.setup(design);
		types.setup_type(primitive, {ID(dataa), ID(datab), ID(datac), ID(datad), ID(cin)}, {ID(combout), ID(cout)}, false, true, false);
	}
	~LutCarryWorker() { log_assert(budget.memory >= owned_memory); budget.memory -= owned_memory; }
	bool reserve(int64_t bytes) { if (!budget.reserve(bytes)) return false; owned_memory += bytes; return true; }
	void release(int64_t bytes) { log_assert(bytes >= 0 && bytes <= owned_memory); owned_memory -= bytes; budget.release(bytes); }

	bool valid_sequential_boundary(Cell *cell) const
	{
		if (StaticCellTypes::categories.is_ff(cell->type)) return true;
		if (cell->type != ID(dffeas) || !types.cell_known(cell->type) || GetSize(cell->connections()) != 10) return false;
		// Intel ff_map 的原生 FF 按真实声明方向检查，未知模块继续进行保守依赖检查。
		for (auto port : {ID(d),ID(clk),ID(clrn),ID(prn),ID(ena),ID(asdata),ID(aload),ID(sclr),ID(sload)})
			if (!cell->hasPort(port) || GetSize(cell->getPort(port)) != 1 ||
				!types.cell_input(cell->type,port) || types.cell_output(cell->type,port)) return false;
		return cell->hasPort(ID(q)) && GetSize(cell->getPort(ID(q))) == 1 &&
			types.cell_output(cell->type,ID(q)) && !types.cell_input(cell->type,ID(q));
	}
	bool sequential(Cell *cell) const { return sequential_cells.count(cell->name); }

	void index_add(Cell *cell)
	{
		bool known = types.cell_known(cell->type);
		auto &ins = cell_inputs[cell->name], &outs = cell_outputs[cell->name];
		for (auto &port : cell->connections()) for (auto bit : sigmap(port.second)) if (bit.wire) {
			if (!known || types.cell_input(cell->type, port.first)) { users[bit][cell->name]++; ins.push_back(bit); }
			if (!known || types.cell_output(cell->type, port.first)) { drivers[bit][cell->name]++; outs.push_back(bit); }
		}
	}
	void index_erase(IdString name)
	{
		for (auto bit : cell_inputs.at(name)) {
			auto &entries = users.at(bit);
			log_assert(entries.at(name) > 0);
			if (--entries.at(name) == 0) entries.erase(name);
		}
		for (auto bit : cell_outputs.at(name)) {
			auto &entries = drivers.at(bit);
			log_assert(entries.at(name) > 0);
			if (--entries.at(name) == 0) entries.erase(name);
		}
		cell_inputs.erase(name); cell_outputs.erase(name);
	}
	IdString driver(SigBit bit) const
	{
		auto it = drivers.find(bit);
		if (!bit.wire || input_counts.count(bit) || it == drivers.end() || it->second.size() != 1 || it->second.begin()->second != 1) return IdString();
		return it->second.begin()->first;
	}
	bool unambiguous(SigBit bit) const
	{
		if (!bit.wire) return constant_bit(bit) >= 0;
		int count = input_counts.count(bit) ? input_counts.at(bit) : 0;
		auto found = drivers.find(bit);
		if (found != drivers.end()) for (auto entry : found->second) count += entry.second;
		return count <= 1;
	}

	bool read_node(Cell *cell, LutCarryNode &node)
	{
		if (!cell) return false;
		if (!cell->type.in(ID($lut), ID($not), ID($_NOT_))) return false;
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::Y) || GetSize(cell->connections()) != 2 || GetSize(cell->getPort(ID::Y)) != 1) return false;
		auto raw = sigmap(cell->getPort(ID::A));
		int width = GetSize(raw);
		Const table;
		if (cell->type == ID($lut)) {
			if (!cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::LUT) || !cell->getParam(ID::WIDTH).is_fully_def() ||
				width > 4 || cell->getParam(ID::WIDTH).as_int() != width) return false;
			table = cell->getParam(ID::LUT);
			if (GetSize(table) != (1 << width) || !table.is_fully_def()) return false;
		} else {
			if (width != 1) return false;
			table = Const(1, 2);
		}
		node.output = sigmap(cell->getPort(ID::Y))[0];
		if (driver(node.output) != cell->name) return false;
		for (auto bit : raw) {
			if (!unambiguous(bit)) return false;
			if (bit.wire) node.inputs.push_back(bit);
		}
		std::sort(node.inputs.begin(), node.inputs.end());
		node.inputs.erase(std::unique(node.inputs.begin(), node.inputs.end()), node.inputs.end());
		for (int address = 0; address < (1 << GetSize(node.inputs)); address++) {
			int original = 0;
			for (int port = 0; port < width; port++) {
				bool value = raw[port] == State::S1;
				if (raw[port].wire) value = (address >> (std::lower_bound(node.inputs.begin(), node.inputs.end(), raw[port]) - node.inputs.begin())) & 1;
				original |= int(value) << port;
			}
			if (table[original] == State::S1) node.truth |= uint16_t(1) << address;
		}
		node.removable = module->selected(cell) && !cell->has_keep_attr() && !cell->get_bool_attribute(ID::lut_keep) && !protected_bits.count(node.output);
		return true;
	}

	bool build_index()
	{
		if (!budget.spend(Lut4Mapping::carry_index_work(module))) return false;
		for (auto wire : module->wires()) for (auto bit : sigmap(wire)) {
			if (wire->port_input && bit.wire) input_counts[bit]++;
			if (wire->port_output || wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep)) observable.insert(bit);
			if (wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep) || wire->attributes.count(ID::init)) protected_bits.insert(bit);
		}
		for (auto cell : module->cells()) {
			index_add(cell);
			if (valid_sequential_boundary(cell)) sequential_cells.insert(cell->name);
		}
		for (auto cell : module->cells()) {
			LutCarryNode node;
			if (read_node(cell, node)) {
				nodes.emplace(cell->name, std::move(node));
				if (cell->attributes.count(ID::src)) source_attributes[cell->name] = cell->attributes.at(ID::src);
			}
		}
		std::map<IdString, int> remaining;
		std::map<IdString, std::set<IdString>> successors;
		for (auto &entry : nodes) {
			std::set<IdString> predecessors;
			for (auto bit : entry.second.inputs) if (nodes.count(driver(bit))) predecessors.insert(driver(bit));
			remaining[entry.first] = GetSize(predecessors);
			for (auto name : predecessors) successors[name].insert(entry.first);
		}
		std::set<IdString> ready;
		for (auto entry : remaining) if (entry.second == 0) ready.insert(entry.first);
		while (!ready.empty()) {
			auto name = *ready.begin(); ready.erase(ready.begin());
			nodes.at(name).rank = GetSize(order);
			order.push_back(name);
			for (auto next : successors[name]) if (--remaining.at(next) == 0) ready.insert(next);
		}
		return true;
	}

	static bool cut_value(const LutCarryCut &cut, const std::vector<SigBit> &leaves, int address)
	{
		int projected = 0;
		for (int port = 0; port < GetSize(cut.leaves); port++) {
			auto it = std::lower_bound(leaves.begin(), leaves.end(), cut.leaves[port]);
			log_assert(it != leaves.end() && *it == cut.leaves[port]);
			projected |= ((address >> (it - leaves.begin())) & 1) << port;
		}
		return (cut.truth >> projected) & 1;
	}
	static bool priority(const LutCarryCut &a, const LutCarryCut &b)
	{
		if (a.nodes.size() != b.nodes.size()) return a.nodes.size() > b.nodes.size();
		return a < b;
	}
	void enumerate_cuts()
	{
		for (auto name : order) {
			if (budget.search_done()) break;
			const auto &node = nodes.at(name);
			if (!node.removable) continue;
			struct Partial { LutCarryCut cut; std::vector<LutCarryCut> inputs; };
			std::vector<Partial> frontier(1);
			for (auto bit : node.inputs) {
				std::vector<LutCarryCut> choices;
				auto source = driver(bit);
				if (cuts.count(source)) choices = cuts.at(source);
				choices.push_back({{bit}, {}, 0xaa});
				std::vector<Partial> next;
				for (const auto &part : frontier) for (const auto &choice : choices) {
					if (!budget.spend(32 + 4 * (part.cut.nodes.size() + choice.nodes.size()))) break;
					Partial result = part;
					result.cut.leaves.insert(result.cut.leaves.end(), choice.leaves.begin(), choice.leaves.end());
					std::sort(result.cut.leaves.begin(), result.cut.leaves.end());
					result.cut.leaves.erase(std::unique(result.cut.leaves.begin(), result.cut.leaves.end()), result.cut.leaves.end());
					if (result.cut.leaves.size() > 3) continue;
					result.cut.nodes.insert(choice.nodes.begin(), choice.nodes.end());
					if (result.cut.nodes.size() >= 64) continue;
					result.inputs.push_back(choice); next.push_back(std::move(result));
					if (next.size() == 64) {
						std::sort(next.begin(), next.end(), [](const Partial &a, const Partial &b) { return priority(a.cut,b.cut); });
						next.resize(32);
					}
				}
				std::sort(next.begin(), next.end(), [](const Partial &a, const Partial &b) { return priority(a.cut, b.cut); });
				if (next.size() > 32) next.resize(32);
				frontier = std::move(next);
				if (budget.search_done() || frontier.empty()) break;
			}
			if (budget.search_done()) break;
			std::map<std::pair<std::vector<SigBit>,uint8_t>,LutCarryCut> unique;
			for (auto &part : frontier) {
				if (!budget.cut() || !budget.prove(8 * (1 + part.inputs.size()))) break;
				part.cut.nodes.insert(name);
				for (int address = 0; address < 8; address++) {
					int original = 0;
					for (int port = 0; port < GetSize(part.inputs); port++) original |= int(cut_value(part.inputs[port], part.cut.leaves, address)) << port;
					if ((node.truth >> original) & 1) part.cut.truth |= uint8_t(1) << address;
				}
				auto key = std::make_pair(part.cut.leaves,part.cut.truth);
				if (!unique.count(key) || priority(part.cut,unique.at(key))) unique[key] = std::move(part.cut);
			}
			auto &result = cuts[name];
			for (auto &entry : unique) result.push_back(std::move(entry.second));
			std::sort(result.begin(), result.end(), priority);
			if (result.size() > 16) result.resize(16);
			for (const auto &cut : result) if (!reserve(512 + 128 * cut.nodes.size())) break;
		}
	}

	bool independent(IdString a, IdString b)
	{
		std::set<IdString> seen;
		std::vector<IdString> pending {a, b};
		while (!pending.empty()) {
			auto current = pending.back(); pending.pop_back();
			for (auto bit : cell_inputs.at(current)) {
				if (!budget.spend(4)) return false;
				auto source = driver(bit);
				if (source == a || source == b) return false;
				auto cell = module->cell(source);
				if (!cell || sequential(cell) || cell->type == primitive) continue;
				if (seen.insert(source).second) pending.push_back(source);
			}
		}
		return true;
	}
	bool fit_pair(IdString sum, const LutCarryCut &s, IdString carry, const LutCarryCut &c, const std::vector<SigBit> &leaves, SigBit cin)
	{
		std::vector<SigBit> operands;
		for (auto bit : leaves) if (bit != cin) operands.push_back(bit);
		if (operands.size() > 2) return false;
		std::vector<std::pair<SigBit, SigBit>> assignments;
		if (operands.size() == 2) assignments.push_back({operands[0], operands[1]});
		else {
			std::vector<SigBit> available = leaves;
			available.push_back(State::S0); available.push_back(State::S1);
			for (auto a : available) for (auto b : available) {
				bool covered = true;
				for (auto bit : operands) if (bit != a && bit != b) covered = false;
				if (covered) assignments.push_back({a,b});
			}
		}
		int initial = constant_bit(cin);
		for (auto operands_pair : assignments) for (int phase = 0; phase < 8; phase++)
			for (bool invert_sum : {false, true}) for (bool invert_carry : {false, true}) {
				if (!budget.spend(16)) return false;
				uint16_t mask = lut_arithmetic_mask(initial, phase, invert_sum, invert_carry);
				bool matches = true;
				for (int address = 0; address < 8 && matches; address++) {
					auto value = [&](SigBit bit) {
						return bit.wire ? bool(address & (1 << (std::lower_bound(leaves.begin(), leaves.end(), bit) - leaves.begin()))) : bit == State::S1;
					};
					int input = int(value(operands_pair.first)) | (int(value(operands_pair.second)) << 1) | (int(value(cin)) << 2);
					matches = bool((mask >> input) & 1) == cut_value(c, leaves, address) && bool((mask >> (input + 8)) & 1) == cut_value(s, leaves, address);
				}
				if (!matches) continue;
				if (!reserve(1536 + 128 * (s.nodes.size() + c.nodes.size()))) return false;
				int index = GetSize(pairs);
				pairs.push_back({sum, carry, s, c, operands_pair.first, operands_pair.second, cin, mask, initial});
				if (cin.wire) cin_pairs[cin].push_back(index);
				return true;
			}
		return false;
	}
	void pair_cuts()
	{
		using Ref = std::pair<IdString, int>;
		std::map<std::vector<SigBit>, std::vector<Ref>> groups;
		std::map<SigBit,std::vector<Ref>> neighbors;
		std::vector<Ref> small;
		for (auto &entry : cuts) for (int i = 0; i < GetSize(entry.second); i++) {
			auto &cut = entry.second[i];
			Ref ref {entry.first,i};
			groups[cut.leaves].push_back(ref);
			for (auto bit : cut.leaves) neighbors[bit].push_back(ref);
			if (cut.leaves.size() <= 2 && small.size() < 32) small.push_back(ref);
		}
		auto compare = [&](Ref sum_ref,Ref carry_ref) {
			if (sum_ref.first == carry_ref.first || !budget.pair() || !budget.spend(8)) return;
			auto &s = cuts.at(sum_ref.first).at(sum_ref.second);
			auto &c = cuts.at(carry_ref.first).at(carry_ref.second);
			std::vector<SigBit> leaves = s.leaves;
			leaves.insert(leaves.end(),c.leaves.begin(),c.leaves.end());
			std::sort(leaves.begin(),leaves.end()); leaves.erase(std::unique(leaves.begin(),leaves.end()),leaves.end());
			if (leaves.size() > 3) return;
			bool parity = true;
			for (int address = 0; address < 8; address++) {
				bool value = s.truth & 1;
				for (int port = 0; port < GetSize(s.leaves); port++)
					if (bool(s.truth & 1) != bool((s.truth >> (1 << port)) & 1)) value ^= bool(address & (1 << port));
				if (value != bool((s.truth >> address) & 1)) parity = false;
			}
			if (!parity || !independent(sum_ref.first,carry_ref.first)) return;
			if (leaves.size() <= 2) fit_pair(sum_ref.first,s,carry_ref.first,c,leaves,State::S0);
			for (auto bit : leaves) fit_pair(sum_ref.first,s,carry_ref.first,c,leaves,bit);
		};
		for (auto &group : groups) {
			if (budget.search_done()) break;
			// 同一个真实共同 cut 的双根先进行函数配对。
			for (auto sum_ref : group.second) for (auto carry_ref : group.second) compare(sum_ref,carry_ref);
		}
		// 不同支持集合使用有限邻接候选，完整共同输入仍由真实 union 决定。
		for (auto &group : groups) for (auto sum_ref : group.second) {
			if (budget.search_done()) return;
			std::set<Ref> candidates;
			for (auto bit : group.first) {
				int examined = 0;
				for (auto ref : neighbors[bit]) {
					if (++examined > 64 || !budget.spend(1)) break;
					if (cuts.at(ref.first).at(ref.second).leaves != group.first) candidates.insert(ref);
				}
			}
			if (group.first.size() <= 1) for (auto ref : small) candidates.insert(ref);
			int examined = 0;
			for (auto ref : candidates) { if (++examined > 32) break; compare(sum_ref,ref); }
		}
	}

	bool valid_pair(int i) const
	{
		const auto &pair = pairs.at(i);
		for (auto name : pair.sum_cut.nodes) if (invalidated.count(name) || !module->cell(name)) return false;
		for (auto name : pair.carry_cut.nodes) if (invalidated.count(name) || !module->cell(name)) return false;
		return true;
	}
	bool price(LutCarryPlan &plan)
	{
		std::set<IdString> region, roots, kept, seen;
		std::set<SigBit> boundary;
		for (int i : plan.path) {
			if (!valid_pair(i) || !budget.spend(8 + 4 * (pairs.at(i).sum_cut.nodes.size() + pairs.at(i).carry_cut.nodes.size()))) return false;
			auto &pair = pairs.at(i);
			if (!roots.insert(pair.sum).second || !roots.insert(pair.carry).second) return false;
			region.insert(pair.sum_cut.nodes.begin(), pair.sum_cut.nodes.end());
			region.insert(pair.carry_cut.nodes.begin(), pair.carry_cut.nodes.end());
			boundary.insert(pair.sum_cut.leaves.begin(), pair.sum_cut.leaves.end());
			boundary.insert(pair.carry_cut.leaves.begin(), pair.carry_cut.leaves.end());
		}
		std::vector<IdString> pending;
		auto keep = [&](IdString name) {
			if (name.empty()) return;
			if (roots.count(name)) { plan.outputs.insert(nodes.at(name).output); return; }
			auto cell = module->cell(name);
			if (!cell || sequential(cell)) return;
			if (region.count(name)) kept.insert(name);
			if (seen.insert(name).second) pending.push_back(name);
		};
		for (auto name : region) {
			if (!budget.spend(4)) return false;
			if (roots.count(name)) continue;
			auto output = nodes.at(name).output;
			if (!nodes.at(name).removable || observable.count(output) || protected_bits.count(output)) keep(name);
			for (auto user : users[output]) if (!region.count(user.first)) keep(name);
		}
		// 新函数叶子的实际前驱全部保留，经过外部组合逻辑的依赖也逐项检查。
		for (auto bit : boundary) if (!roots.count(driver(bit))) keep(driver(bit));
		while (!pending.empty()) {
			auto name = pending.back(); pending.pop_back();
			for (auto bit : cell_inputs.at(name)) { if (!budget.spend(4)) return false; keep(driver(bit)); }
		}
		for (auto name : region) if (!kept.count(name)) plan.deleting.insert(name);
		for (auto bit : boundary) if (plan.deleting.count(driver(bit)) && !roots.count(driver(bit)))
			log_error("LUT carry deletion owns a replacement input.\n");
		std::map<IdString, int> stage;
		for (int p = 0; p < GetSize(plan.path); p++) { auto &pair = pairs.at(plan.path[p]); stage[pair.sum] = stage[pair.carry] = p; }
		for (int p = 0; p < GetSize(plan.path); p++) {
			auto &pair = pairs.at(plan.path[p]);
			for (auto bit : {pair.a, pair.b, pair.cin}) {
				std::vector<IdString> ancestors {driver(bit)};
				std::set<IdString> visited;
				while (!ancestors.empty()) {
					if (!budget.spend(4)) return false;
					auto source = ancestors.back(); ancestors.pop_back();
					if (stage.count(source)) { if (stage.at(source) >= p) return false; continue; }
					auto cell = module->cell(source);
					if (!cell || sequential(cell) || !visited.insert(source).second) continue;
					for (auto input : cell_inputs.at(source)) ancestors.push_back(driver(input));
				}
			}
		}
		for (auto name : plan.deleting) {
			auto output = nodes.at(name).output;
			bool outside = observable.count(output) || protected_bits.count(output);
			for (auto user : users[output]) if (!plan.deleting.count(user.first)) outside = true;
			if (outside) {
				if (!roots.count(name)) log_error("LUT carry deletion has an unowned external output.\n");
				plan.outputs.insert(output);
			}
		}
		// 被区域内部新函数读取的根同样需要真实普通输出。
		for (int p = 0; p < GetSize(plan.path); p++) {
			auto &pair = pairs.at(plan.path[p]);
			for (auto bit : {pair.a,pair.b,pair.cin}) if (roots.count(driver(bit))) {
				bool dedicated = p > 0 && bit == pair.cin && bit == nodes.at(pairs.at(plan.path[p-1]).carry).output;
				if (!dedicated || bit == pair.a || bit == pair.b) plan.outputs.insert(bit);
			}
		}
		int segment = 0, position = 0;
		SigBit ordinary = State::Sx;
		auto add = [&](CarryRole role, int i, SigBit input, SigBit output, uint16_t mask) {
			plan.steps.push_back({i,segment,position++,role,input,output,mask});
		};
		for (int p = 0; p < GetSize(plan.path); p++) {
			int i = plan.path[p]; auto &pair = pairs.at(i);
			auto sum = nodes.at(pair.sum).output, carry = nodes.at(pair.carry).output;
			bool need_sum = plan.outputs.count(sum), need_carry = plan.outputs.count(carry);
			if (p == 0 && pair.initial < 0) add(CarryRole::Start, i, pair.cin, State::Sx, 0xaaaa);
			int required = 1 + int(need_sum && need_carry);
			if (position + required + int(p+1 < GetSize(plan.path)) > 16) {
				if (!ordinary.wire) {
					auto previous = nodes.at(pairs.at(plan.path[p-1]).carry).output;
					add(CarryRole::Export, plan.path[p-1], State::Sx, previous, 0xf0f0); ordinary = previous;
				}
				log_assert(position <= 16);
				segment++; position = 0;
				add(CarryRole::Start, i, ordinary, State::Sx, 0xaaaa);
			}
			uint16_t mask = need_sum ? pair.mask : (pair.mask & 0xff) * 0x101;
			add(CarryRole::Arithmetic, i, State::Sx, need_sum ? sum : need_carry ? carry : SigBit(State::Sx), mask);
			ordinary = !need_sum && need_carry ? carry : SigBit(State::Sx);
			if (need_sum && need_carry) { add(CarryRole::Export, i, State::Sx, carry, 0xf0f0); ordinary = carry; }
			log_assert(position <= 16);
		}
		plan.gain = GetSize(plan.deleting) - GetSize(plan.steps);
		return plan.gain > 0;
	}

	bool prove(const LutCarryPlan &plan)
	{
		std::set<SigBit> proven_outputs;
		for (int i : plan.path) {
			auto &pair = pairs.at(i);
			std::vector<SigBit> leaves = pair.sum_cut.leaves;
			leaves.insert(leaves.end(), pair.carry_cut.leaves.begin(), pair.carry_cut.leaves.end());
			std::sort(leaves.begin(), leaves.end()); leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
			if (!budget.prove(8 * (8 + pair.sum_cut.nodes.size() + pair.carry_cut.nodes.size()))) return false;
			std::map<IdString,LutCarryNode> actual;
			std::vector<IdString> proof_order;
			std::set<IdString> cone = pair.sum_cut.nodes;
			cone.insert(pair.carry_cut.nodes.begin(),pair.carry_cut.nodes.end());
			for (auto name : cone) {
				LutCarryNode node;
				if (!read_node(module->cell(name),node)) log_error("LUT carry proof encountered a changed cell.\n");
				actual.emplace(name,std::move(node)); proof_order.push_back(name);
			}
			std::sort(proof_order.begin(),proof_order.end(),[&](IdString a,IdString b) { return nodes.at(a).rank < nodes.at(b).rank; });
			// 独立计算真实区域，避免使用候选生成时的函数缓存作为证明。
			auto evaluate = [&](const LutCarryCut &cut, int address) {
				std::map<SigBit,bool> values;
				for (int port = 0; port < GetSize(leaves); port++) values[leaves[port]] = bool(address & (1 << port));
				for (auto name : proof_order) if (cut.nodes.count(name)) {
					const auto &node = actual.at(name);
					int input = 0;
					for (int port = 0; port < GetSize(node.inputs); port++) {
						if (!values.count(node.inputs[port])) log_error("LUT carry truth proof has an incomplete boundary.\n");
						input |= int(values.at(node.inputs[port])) << port;
					}
					values[node.output] = (node.truth >> input) & 1;
				}
				auto root = nodes.at(cut.nodes.count(pair.sum) ? pair.sum : pair.carry).output;
				return values.at(root);
			};
			for (int address = 0; address < 8; address++) {
				auto value = [&](SigBit bit) { return bit.wire ? bool(address & (1 << (std::lower_bound(leaves.begin(), leaves.end(), bit) - leaves.begin()))) : bit == State::S1; };
				int input = int(value(pair.a)) | (int(value(pair.b)) << 1) | (int(value(pair.cin)) << 2);
				if (evaluate(pair.sum_cut,address) != (primitive_lut(pair.mask,{value(pair.a) ? State::S1 : State::S0,value(pair.b) ? State::S1 : State::S0,value(pair.cin) ? State::S1 : State::S0,State::S1}) == State::S1) ||
					evaluate(pair.carry_cut,address) != bool((pair.mask >> input) & 1)) log_error("LUT carry arithmetic truth proof failed.\n");
			}
			proven_outputs.insert(nodes.at(pair.sum).output); proven_outputs.insert(nodes.at(pair.carry).output);
		}
		for (auto bit : plan.outputs) if (!proven_outputs.count(bit)) log_error("LUT carry proof omitted an external observation.\n");
		for (auto &step : plan.steps) {
			if (!budget.prove(128)) return false;
			const auto &pair = pairs.at(step.pair);
			for (int address = 0; address < 8; address++) {
				bool expected_low = (step.mask >> address) & 1;
				bool expected_high = (step.mask >> (address+8)) & 1;
				if (step.role == CarryRole::Start) {
					if (expected_low != bool(address & 1) || expected_high != bool(address & 1)) log_error("LUT carry injection truth proof failed.\n");
				} else if (step.role == CarryRole::Export) {
					if (expected_low != bool(address & 4) || expected_high != bool(address & 4)) log_error("LUT carry export truth proof failed.\n");
				} else {
					bool low = (pair.mask >> address) & 1;
					bool high = (pair.mask >> (address+8)) & 1;
					bool sum_output = step.output == nodes.at(pair.sum).output;
					if (expected_low != low || expected_high != (sum_output ? high : low)) log_error("LUT carry emitted output truth proof failed.\n");
				}
			}
		}
		return true;
	}

	void commit(const LutCarryPlan &plan)
	{
		log_assert(plan.gain > 0 && GetSize(plan.deleting) > GetSize(plan.steps));
		if (!reserve(1024 + 1536 * plan.steps.size()) || !budget.spend(32 * plan.deleting.size() + 64 * plan.steps.size())) return;
		// 下游函数缓存按代次失效；名称引用在删除后不会保留悬空指针。
		std::deque<IdString> pending(plan.deleting.begin(),plan.deleting.end());
		while (!pending.empty()) {
			auto name = pending.front(); pending.pop_front();
			if (!invalidated.insert(name).second) continue;
			for (auto bit : cell_outputs.at(name)) for (auto user : users[bit])
				if (nodes.count(user.first) && !invalidated.count(user.first)) pending.push_back(user.first);
		}
		generation++;
		std::string chain_name = stringf("lut:%s:%llu", pairs.at(plan.path.front()).carry.c_str(), (unsigned long long)generation);
		for (auto name : plan.deleting) { log_assert(nodes.at(name).removable); index_erase(name); }
		for (auto name : plan.deleting) module->remove(module->cell(name));
		SigBit carry = State::Sx;
		int count = 0;
		for (const auto &step : plan.steps) {
			const auto &pair = pairs.at(step.pair);
			auto out = step.output.wire ? step.output : SigBit(module->addWire(NEW_ID));
			auto next = SigBit(module->addWire(NEW_ID));
			auto cell = module->addCell(NEW_ID,primitive);
			cell->setParam(ID(lut_mask),Const(step.mask,16));
			cell->setParam(ID(sum_lutc_input),Const("cin"));
			cell->setParam(ID(dont_touch),Const("on"));
			cell->setParam(ID(lpm_type),Const("cycloneiv_lcell_comb"));
			cell->setPort(ID(dataa),step.role == CarryRole::Start ? step.input : step.role == CarryRole::Export ? SigBit(State::S0) : pair.a);
			cell->setPort(ID(datab),step.role == CarryRole::Arithmetic ? pair.b : SigBit(State::S0));
			cell->setPort(ID(datac),State::S0); cell->setPort(ID(datad),State::S1);
			bool first = step.role == CarryRole::Arithmetic && step.position == 0 && pair.initial >= 0;
			cell->setPort(ID(cin),step.role == CarryRole::Start || first ? SigBit(State::Sx) : carry);
			cell->setPort(ID(combout),out); cell->setPort(ID(cout),next);
			cell->attributes[ID(cycloneiv_carry_mask)] = Const(step.mask,16);
			cell->attributes[role_attr] = Const(step.role == CarryRole::Start ? "start" : step.role == CarryRole::Export ? "export" : first ? "lut_first" : "lut_arithmetic");
			cell->attributes[chain_attr] = Const(stringf("%s:%d",chain_name.c_str(),step.segment));
			cell->attributes[index_attr] = Const(step.position);
			if (source_attributes.count(pair.sum)) cell->attributes[ID::src] = source_attributes.at(pair.sum);
			index_add(cell); carry = next; count++;
		}
		log_assert(count == GetSize(plan.steps));
		for (auto bit : plan.outputs) if (driver(bit).empty()) log_error("LUT carry emission omitted a live output.\n");
		accepted++; deleted += GetSize(plan.deleting); added += count;
		design->scratchpad_set_bool("opt.did_something",true);
		log("LUT carry %s: stages=%d delete=%d add=%d gain=%d generation=%llu.\n",log_id(module),GetSize(plan.path),GetSize(plan.deleting),count,plan.gain,(unsigned long long)generation);
	}

	void run()
	{
		budget.phase("cuts",1);
		if (!build_index()) return;
		Lut4Mapping::PostTimer search_timer(Lut4Mapping::timed_post_design(design), Lut4Mapping::PostPhase::CarrySearch);
		enumerate_cuts();
		if (budget.stopped) return;
		budget.phase("pairs",2);
		pair_cuts();
		if (budget.stopped) return;
		budget.phase("paths",3);
		std::vector<LutCarryPlan> plans;
		auto plan_bytes = [](const LutCarryPlan &plan) { return int64_t(1024 + 128 * plan.deleting.size() + 256 * plan.steps.size()); };
		auto better = [](const LutCarryPlan &a,const LutCarryPlan &b) { if (a.gain != b.gain) return a.gain > b.gain; return a.path < b.path; };
		std::vector<int> roots_order;
		for (int i = 0; i < GetSize(pairs); i++) roots_order.push_back(i);
		std::sort(roots_order.begin(),roots_order.end(),[&](int a,int b) {
			int ra = nodes.at(pairs[a].carry).rank, rb = nodes.at(pairs[b].carry).rank;
			return ra != rb ? ra < rb : a < b;
		});
		for (int root : roots_order) {
			if (budget.search_done()) break;
			LutCarryPlan current; current.path.push_back(root);
			LutCarryPlan best;
			std::set<IdString> roots {pairs[root].sum,pairs[root].carry};
			for (int length = 0; length < 64; length++) {
				if (!budget.spend(32)) break;
				LutCarryPlan priced = current;
				if (price(priced) && better(priced,best)) best = std::move(priced);
				int chosen = -1;
				auto bit = nodes.at(pairs.at(current.path.back()).carry).output;
				for (int i : cin_pairs[bit]) {
					if (!budget.spend(4)) break;
					if (roots.count(pairs[i].sum) || roots.count(pairs[i].carry)) continue;
					if (chosen < 0 || pairs[i].sum_cut.nodes.size() + pairs[i].carry_cut.nodes.size() >
						pairs[chosen].sum_cut.nodes.size() + pairs[chosen].carry_cut.nodes.size()) chosen = i;
				}
				if (chosen < 0 || budget.search_done()) break;
				current.path.push_back(chosen); roots.insert(pairs[chosen].sum); roots.insert(pairs[chosen].carry);
			}
			if (best.gain > 0) {
				// 保留有限完整计划，搜索停止后使用共同预算的预留部分完成证明。
				if (plans.size() == 32) {
					std::sort(plans.begin(),plans.end(),better);
					if (!better(best,plans.back())) continue;
					release(plan_bytes(plans.back())); plans.pop_back();
				}
				bool search_was_stopped = budget.search_stopped;
				budget.finish_search();
				bool room = plan_bytes(best) <= budget.memory_limit - budget.memory - budget.memory_limit / 16;
				bool stored = room && reserve(plan_bytes(best));
				budget.searching = true;
				budget.search_stopped = search_was_stopped;
				if (stored) plans.push_back(std::move(best));
				if (!room) {
					budget.search_stopped = true;
					if (!budget.search_reason.empty()) budget.search_reason += "; ";
					budget.search_reason += "paths: reserved proof workspace";
				}
			}
		}
		budget.finish_search();
		std::sort(plans.begin(),plans.end(),better);
		for (auto &old : plans) {
			if (budget.stopped) break;
			LutCarryPlan current; current.path = old.path;
			if (price(current) && prove(current)) commit(current);
		}
		log("LUT carry search %s: roots=%d candidates=%d plans=%d accepted=%d deleted=%d added=%d.\n",
			log_id(module),GetSize(cuts),GetSize(pairs),GetSize(plans),accepted,deleted,added);
	}
};

static void map_lut_carry(Design *design, const LutCarryOptions &requested)
{
	LutCarryOptions options = requested;
	if (Lut4Mapping::shared_post(design)) {
		auto restrict_limit = [&](int64_t &limit, const std::string &key) {
			int64_t remaining = std::stoll(design->scratchpad_get_string(key));
			limit = limit < 0 ? remaining : std::min(limit, remaining);
		};
		restrict_limit(options.max_work, Lut4Mapping::post_key("carry", "remaining"));
		restrict_limit(options.max_proof, Lut4Mapping::post_key("carry", "truth_remaining"));
		restrict_limit(options.max_memory, "opt_lut4_post.memory_remaining");
	}
	int64_t scale = 0;
	bool zero = options.max_cuts == 0 || options.max_pairs == 0 || options.max_work == 0 || options.max_proof == 0 || options.max_memory == 0;
	if (!zero) {
		if (Lut4Mapping::shared_post(design)) scale = std::stoll(design->scratchpad_get_string(Lut4Mapping::post_key("carry", "scale")));
		else scale = Lut4Mapping::carry_scale(design);
	}
	// 共享余额仍受当前剩余 LUT 网络的单次规模上限约束。
	if (Lut4Mapping::shared_post(design)) {
		options.max_work = std::min(options.max_work, std::min<int64_t>(24000000, 8192 * scale));
		options.max_proof = std::min(options.max_proof, std::min<int64_t>(4000000, 2048 * scale));
		options.max_memory = std::min(options.max_memory, std::min<int64_t>(96 * 1048576, 8 * 1048576 + 8192 * scale));
	}
	LutCarryBudget budget(options,scale);
	budget.finish_search();
	int64_t audit_capacity = 0;
	int64_t audit_reservation = 0;
	if (!budget.stopped) {
		for (auto module : design->selected_modules()) if (!module->get_blackbox_attribute() && !module->has_processes()) {
			audit_capacity = std::max(audit_capacity,Lut4Mapping::carry_index_bytes(module));
			audit_reservation = Lut4Mapping::capacity_add(audit_reservation,Lut4Mapping::carry_index_work(module));
		}
		// 完整 audit 的索引遍历及新增端口空间从当前同一工作余额预留。
		audit_reservation = Lut4Mapping::capacity_add(Lut4Mapping::capacity_mul(2,audit_reservation),Lut4Mapping::capacity_mul(256,scale));
	}
	if (audit_capacity > budget.memory_limit) budget.stop("complete carry index memory limit");
	if (audit_reservation >= budget.work_limit) { budget.stop("complete carry audit work limit"); audit_reservation = 0; }
	budget.work_limit -= audit_reservation;
	for (auto module : design->selected_modules()) {
		if (budget.stopped) break;
		if (module->get_blackbox_attribute() || module->has_processes()) continue;
		// SigMap、CellTypes 及完整图索引在构造之前使用同一峰值预留。
		int64_t index = Lut4Mapping::carry_index_bytes(module);
		if (!budget.reserve(index)) break;
		bool accepted = false;
		{
			LutCarryWorker worker(design,module,budget);
			worker.owned_memory = index;
			worker.run();
			accepted = worker.accepted != 0;
		}
		if (accepted) {
			budget.peak_memory = std::max(budget.peak_memory,Lut4Mapping::carry_index_bytes(module));
			int64_t cleanup_work = Lut4Mapping::carry_index_work(module);
			log_assert(cleanup_work <= audit_reservation);
			audit_reservation -= cleanup_work;
			budget.work += cleanup_work;
			budget.work_limit += cleanup_work;
			clean_generated(design,module,false);
		}
	}
	if (!zero && budget.peak_memory) for (auto module : design->selected_modules()) if (!module->get_blackbox_attribute() && !module->has_processes()) {
		budget.peak_memory = std::max(budget.peak_memory,Lut4Mapping::carry_index_bytes(module));
		int64_t audit_work = Lut4Mapping::carry_index_work(module);
		log_assert(audit_work <= audit_reservation);
		audit_reservation -= audit_work;
		budget.work += audit_work;
		audit_carry(design,module);
	}
	budget.work_limit = options.max_work >= 0 ? options.max_work : std::min<int64_t>(24000000,8192 * std::max<int64_t>(1,scale));
	Lut4Mapping::report_carry(design,budget.work,budget.proof,budget.peak_memory);
	log("LUT carry design resources: cuts=%lld/%lld pairs=%lld/%lld work=%lld/%lld truth=%lld/%lld peak-workspace-bytes=%lld/%lld search-stop=%s total-stop=%s.\n",
		(long long)budget.cuts,(long long)budget.cuts_limit,(long long)budget.pairs,(long long)budget.pairs_limit,
		(long long)budget.work,(long long)budget.work_limit,(long long)budget.proof,(long long)budget.proof_limit,
		(long long)budget.peak_memory,(long long)budget.memory_limit,budget.search_reason.empty() ? "no" : budget.search_reason.c_str(),budget.stopped ? budget.reason.c_str() : "no");
}
