// 本文件在 LutResynWorker 内部引入，共享真实索引、器件边界及资源账户。
struct DictionaryEntry
{
	vector<int> support;
	LutResynTable table, signature;
	SigBit existing;
	IdString owner;
	bool is_existing = false;
};

enum class DictionaryOutputKind { Rebuild, PreserveRoot };

struct DictionaryOutput
{
	// 非负编号引用 dictionary，负数 -1-i 引用第 i 个独立边界输入。
	vector<int> inputs;
	LutResynTable table;
	DictionaryOutputKind kind = DictionaryOutputKind::Rebuild;
	std::set<int> functions;
};

struct DictionaryPartial
{
	vector<DictionaryOutput> outputs;
	std::set<int> functions;
	std::set<IdString> retained;
	int estimate = 0;
};

struct DictionarySeed
{
	vector<unsigned> bound;
	vector<LutResynTable> tables;
	unsigned top = 0;
};

struct DictionaryProblem
{
	int width;
	vector<LutResynTable> value;
	LutResynTable care;
	bool operator<(const DictionaryProblem &other) const {
		return std::tie(width, value, care) < std::tie(other.width, other.value, other.care);
	}
};

struct DictionaryCachedProblem
{
	vector<DictionarySeed> seeds;
	int64_t bytes = 0;
};

std::map<DictionaryProblem, DictionaryCachedProblem> dictionary_problem_cache;

bool dictionary_charge(int64_t amount, int64_t &category) {
	if (!resources.spend(amount)) return false;
	category += amount;
	return true;
}

// 全部高位保持零值，局部表与区域表使用明确的有效赋值范围。
LutResynTable dictionary_expand(const vector<int> &support, const LutResynTable &table, int width) const {
	LutResynTable result;
	for (int a = 0; a < (1 << width); a++) result.set(a, table.get(lutresyn_project(a, support)));
	return result;
}

bool dictionary_values(const LutResynRegion &region, std::map<SigBit, LutResynTable> &values) {
	int rows = 1 << GetSize(region.boundary), blocks = (rows + 63) / 64;
	int64_t work = rows * GetSize(region.boundary);
	for (auto name : region.order) {
		Cell *cell = module->cell(name);
		work += blocks * GetSize(lutresyn_logic_table(cell)) * (GetSize(cell->getPort(ID::A)) + 2) + 16;
	}
	if (!dictionary_charge(work, proof_work)) return false;
	for (int i = 0; i < GetSize(region.boundary); i++) {
		LutResynTable value;
		for (int a = 0; a < rows; a++) value.set(a, (a >> i) & 1);
		values.emplace(region.boundary[i], value);
	}
	for (auto name : region.order) {
		Cell *cell = module->cell(name);
		vector<LutResynTable> inputs;
		for (auto bit : cell->getPort(ID::A)) {
			bit = canonical(bit);
			LutResynTable value;
			if (bit.wire) value = values.at(bit);
			else if (bit == State::S1)
				for (int a = 0; a < rows; a++) value.set(a, true);
			inputs.push_back(value);
		}
		LutResynTable result;
		Const mask = lutresyn_logic_table(cell);
		for (int a = 0; a < GetSize(mask); a++) if (mask[a] == State::S1)
			for (int block = 0; block < blocks; block++) {
				uint64_t product = ~uint64_t(0);
				for (int i = 0; i < GetSize(inputs); i++)
					product &= (a >> i) & 1 ? inputs[i].words[block] : ~inputs[i].words[block];
				result.words[block] |= product;
			}
		if (rows < 64) result.words[0] &= (uint64_t(1) << rows) - 1;
		values.emplace(canonical(cell->getPort(ID::Y)[0]), result);
	}
	return true;
}

// 真实组合 cut 的全部前沿赋值构成环境域，前沿信号均独立枚举。
bool dictionary_environment(const LutResynRegion &region, LutResynTable &care) {
	std::set<IdString> nodes;
	std::set<SigBit> leaves(region.boundary.begin(), region.boundary.end());
	bool changed = true;
	while (changed && GetSize(nodes) < 128) {
		changed = false;
		vector<SigBit> frontier(leaves.begin(), leaves.end());
		for (auto bit : frontier) {
			if (!dictionary_charge(8, environment_work)) return false;
			Cell *driver = unique_driver(bit);
			if (!driver || sequential(driver) || !valid_lut(driver, false) || region.nodes.count(driver->name) || nodes.count(driver->name)) continue;
			std::set<SigBit> next = leaves;
			next.erase(bit);
			for (auto predecessor : driver->getPort(ID::A)) {
				predecessor = canonical(predecessor);
				if (!predecessor.wire) continue;
				Cell *source = unique_driver(predecessor);
				if (!source || !nodes.count(source->name)) next.insert(predecessor);
			}
			if (GetSize(next) > 10) continue;
			nodes.insert(driver->name); leaves = std::move(next); changed = true;
			if (GetSize(nodes) == 128) break;
		}
	}
	if (nodes.empty()) return false;
	int rows = 1 << GetSize(leaves);
	int64_t needed_work = rows * (GetSize(nodes) * 7 + GetSize(region.boundary) + 1);
	// 环境枚举费用有明确上界，搜索与联合证明继续保有工作额度。
	if (needed_work > (resources.local_limit - resources.work) / 4) return false;
	if (!dictionary_charge(needed_work, environment_work)) return false;
	vector<SigBit> independent_inputs(leaves.begin(), leaves.end());
	std::map<IdString, int> degree;
	std::map<IdString, vector<IdString>> successors;
	std::set<IdString> ready;
	for (auto name : nodes) {
		std::set<IdString> predecessors;
		for (auto bit : cell_inputs.at(name)) {
			Cell *driver = unique_driver(bit);
			if (driver && nodes.count(driver->name)) predecessors.insert(driver->name);
		}
		degree[name] = GetSize(predecessors);
		for (auto predecessor : predecessors) successors[predecessor].push_back(name);
		if (predecessors.empty()) ready.insert(name);
	}
	vector<IdString> order;
	while (!ready.empty()) {
		IdString name = *ready.begin(); ready.erase(ready.begin()); order.push_back(name);
		for (auto successor : successors[name]) if (--degree.at(successor) == 0) ready.insert(successor);
	}
	log_assert(GetSize(order) == GetSize(nodes));
	LutResynTable reachable;
	for (int a = 0; a < rows; a++) {
		std::map<SigBit, bool> values;
		for (int i = 0; i < GetSize(independent_inputs); i++) values[independent_inputs[i]] = (a >> i) & 1;
		for (auto name : order) {
			Cell *cell = module->cell(name);
			int address = 0, i = 0;
			for (auto bit : cell->getPort(ID::A)) {
				bit = canonical(bit);
				address |= int(bit.wire ? values.at(bit) : bit == State::S1) << i++;
			}
			values[canonical(cell->getPort(ID::Y)[0])] = lutresyn_logic_table(cell)[address] == State::S1;
		}
		int address = 0;
		for (int i = 0; i < GetSize(region.boundary); i++) address |= int(values.at(region.boundary[i])) << i;
		reachable.set(address, true);
	}
	care = reachable;
	care_regions++;
	return true;
}

int dictionary_add(vector<DictionaryEntry> &dictionary, DictionaryEntry entry, int width) {
	if (!dictionary_charge(32 + (1 << std::min(4, GetSize(entry.support))) * (GetSize(entry.support) + 1) + GetSize(dictionary) * 32, dictionary_work)) return -1;
	if (!entry.is_existing) {
		lutresyn_reduce(entry.support, entry.table);
		if (entry.table.get(0))
			for (int a = 0; a < (1 << GetSize(entry.support)); a++) entry.table.set(a, !entry.table.get(a));
	}
	int existing_count = 0, new_count = 0;
	for (int i = 0; i < GetSize(dictionary); i++) {
		const auto &previous = dictionary[i];
		if (previous.is_existing) existing_count++; else new_count++;
		if (entry.is_existing && previous.is_existing && previous.existing == entry.existing) return i;
		if (!entry.is_existing && !previous.is_existing && previous.support == entry.support && previous.table == entry.table) return i;
	}
	if ((entry.is_existing ? existing_count : new_count) >= 32) return -1;
	if (!entry.is_existing) {
		if (!dictionary_charge((1 << width) * (GetSize(entry.support) + 1), dictionary_work)) return -1;
		entry.signature = dictionary_expand(entry.support, entry.table, width);
	}
	dictionary.push_back(std::move(entry));
	dictionary_functions++;
	return GetSize(dictionary) - 1;
}

bool dictionary_fit(const vector<DictionaryEntry> &dictionary, const LutResynTable &value,
                    const LutResynTable &care, int width, vector<int> inputs, DictionaryOutput &output) {
	std::sort(inputs.begin(), inputs.end());
	inputs.erase(std::unique(inputs.begin(), inputs.end()), inputs.end());
	if (GetSize(inputs) > 4) return false;
	if (!dictionary_charge(16 + (1 << width) * (GetSize(inputs) + 2), address_work)) return false;
	int known[16]; std::fill(known, known + 16, -1);
	LutResynTable mask;
	for (int a = 0; a < (1 << width); a++) if (care.get(a)) {
		int address = 0;
		for (int i = 0; i < GetSize(inputs); i++) {
			int input = inputs[i];
			bool bit = input < 0 ? (a >> (-1 - input)) & 1 : dictionary.at(input).signature.get(a);
			address |= int(bit) << i;
		}
		int result = value.get(a);
		if (known[address] >= 0 && known[address] != result) return false;
		known[address] = result; mask.set(address, result);
	}
	lutresyn_reduce(inputs, mask);
	output.inputs = std::move(inputs); output.table = mask;
	for (int input : output.inputs) if (input >= 0) output.functions.insert(input);
	return true;
}

void dictionary_keep_candidate(vector<DictionaryOutput> &choices, DictionaryOutput candidate) {
	if (!dictionary_charge(16 * GetSize(choices) + 8, address_work)) return;
	for (const auto &previous : choices)
		if (previous.kind == candidate.kind && previous.inputs == candidate.inputs && previous.table == candidate.table) return;
	if (GetSize(choices) < 8) choices.push_back(std::move(candidate));
}

// 有限 AC 列分类同时支持一个与两个编码函数，以及 bound/top 共有变量。
bool dictionary_decompose(const DictionaryProblem &problem, vector<DictionarySeed> &seeds) {
	int width = problem.width;
	unsigned all = (1u << width) - 1;
	for (int bridges = 1; bridges <= 2; bridges++) {
	for (unsigned bound = 1; bound <= all; bound++) {
		if (!dictionary_charge(1, dictionary_work)) return false;
		if (lutresyn_count(bound) > 4) continue;
		unsigned free = all & ~bound;
		for (unsigned common = bound;; common = (common - 1) & bound) {
			if (!dictionary_charge(1, dictionary_work)) return false;
			unsigned top = free | common;
			// bridges 提升为最外层循环后，这里必须复现原内层循环的 continue 语义：
			// 跳过本次循环体，但仍执行 common==0 的终止检查。
			if (lutresyn_count(top) + bridges > 4) {
				if (!common) break;
				continue;
			}
			int64_t charge = 16 + (1 << width) * GetSize(problem.value) * 3;
			if (!dictionary_charge(charge, dictionary_work)) return false;
			auto bp = lutresyn_positions(bound), cp = lutresyn_positions(common);
			auto xp = lutresyn_positions(bound & ~common), fp = lutresyn_positions(free);
			vector<vector<int>> codes(1 << GetSize(cp));
			int maximum_classes = 0;
			bool valid = true;
			for (int ca = 0; ca < GetSize(codes) && valid; ca++) {
				vector<uint64_t> columns, cares;
				for (int xa = 0; xa < (1 << GetSize(xp)); xa++) {
					uint64_t column = 0, cared = 0;
					for (int o = 0; o < GetSize(problem.value); o++)
						for (int fa = 0; fa < (1 << GetSize(fp)); fa++) {
							int a = lutresyn_deposit(ca, cp) | lutresyn_deposit(xa, xp) | lutresyn_deposit(fa, fp);
							int index = o * (1 << GetSize(fp)) + fa;
							if (problem.care.get(a)) cared |= uint64_t(1) << index;
							if (problem.value[o].get(a)) column |= uint64_t(1) << index;
						}
					int code = 0;
					for (; code < GetSize(columns); code++) {
						if (!dictionary_charge(1, dictionary_work)) return false;
						if (((columns[code] ^ column) & cares[code] & cared) == 0) break;
					}
					if (code == GetSize(columns)) {
						if (code == (1 << bridges)) { valid = false; break; }
						columns.push_back(column & cared); cares.push_back(cared);
					} else {
						columns[code] = (columns[code] & cares[code]) | (column & cared);
						cares[code] |= cared;
					}
					codes[ca].push_back(code);
				}
				maximum_classes = std::max(maximum_classes, GetSize(columns));
			}
			if (!valid || maximum_classes <= 1 || (bridges == 2 && maximum_classes <= 2)) {
				if (!common) break;
				continue;
			}
			vector<int> encoding(1 << bridges);
			for (int i = 0; i < GetSize(encoding); i++) encoding[i] = i;
			do {
				int phases = bridges == 1 ? (1 << GetSize(codes)) : 1;
				for (int phase = 0; phase < phases; phase++) {
				if (!dictionary_charge(16 * bridges, dictionary_work)) return false;
				DictionarySeed seed; seed.top = top;
				seed.bound.assign(bridges, bound); seed.tables.resize(bridges);
				for (int ca = 0; ca < GetSize(codes); ca++)
					for (int xa = 0; xa < GetSize(codes[ca]); xa++) {
						int ba = lutresyn_project(lutresyn_deposit(ca, cp) | lutresyn_deposit(xa, xp), bp);
						int code = encoding[codes[ca][xa]] ^ (bridges == 1 ? ((phase >> ca) & 1) : 0);
						for (int i = 0; i < bridges; i++) seed.tables[i].set(ba, (code >> i) & 1);
					}
				seeds.push_back(std::move(seed));
				if (GetSize(seeds) >= 96) return true;
				}
			} while (bridges == 2 && std::next_permutation(encoding.begin(), encoding.end()));
			if (!common) break;
		}
	}
	}
	return true;
}

bool dictionary_price(const LutResynRegion &region, LutResynPlan &plan) {
	int64_t work = 64 + 32 * GetSize(region.nodes) + 16 * (GetSize(plan.outputs) + 5 * GetSize(plan.nodes));
	for (auto name : region.nodes) {
		SigBit output = canonical(module->cell(name)->getPort(ID::Y)[0]);
		auto found = users.find(output);
		if (found != users.end()) work += 8 * GetSize(found->second);
	}
	if (!dictionary_charge(work, price_work)) return false;
	std::set<IdString> replaced;
	vector<IdString> preserve_queue;
	for (int o = 0; o < GetSize(region.roots); o++) {
		if (plan.preserve[o]) preserve_queue.push_back(region.roots[o]);
		else replaced.insert(region.roots[o]);
	}
	plan.cost();
	auto retain_ref = [&](LutResynRef ref) {
		if (ref.node >= 0 || !ref.bit.wire) return;
		Cell *driver = unique_driver(ref.bit);
		if (driver && region.nodes.count(driver->name)) preserve_queue.push_back(driver->name);
	};
	for (auto ref : plan.outputs) retain_ref(ref);
	for (int i : plan.needed) for (auto ref : plan.nodes[i].inputs) retain_ref(ref);
	while (!preserve_queue.empty()) {
		IdString name = preserve_queue.back(); preserve_queue.pop_back();
		if (replaced.count(name)) { log_debug("  Dictionary price rejected rebuilt dependency %s.\n", log_id(name)); return false; }
		if (!plan.retained.insert(name).second) continue;
		for (auto bit : cell_inputs.at(name)) {
			Cell *driver = unique_driver(bit);
			if (driver && region.nodes.count(driver->name)) preserve_queue.push_back(driver->name);
		}
	}
	for (auto name : region.nodes) if (!plan.retained.count(name)) plan.deleting.insert(name);
	for (auto name : plan.deleting) {
		Cell *cell = module->cell(name);
		if (!valid_lut(cell, true)) return false;
		SigBit output = canonical(cell->getPort(ID::Y)[0]);
		if (ports_out.count(output) && !replaced.count(name)) return false;
		auto found = users.find(output);
		if (found != users.end()) for (auto user : found->second)
			if (!plan.deleting.count(user) && !replaced.count(name)) return false;
	}
	for (int i : plan.needed) for (auto ref : plan.nodes[i].inputs) {
		if (ref.node >= 0) { if (ref.node >= i) return false; }
		else {
			Cell *driver = unique_driver(ref.bit);
			if (driver && plan.deleting.count(driver->name)) return false;
		}
	}
	plan.gain = GetSize(plan.deleting) - GetSize(plan.needed);
	log_debug("  Dictionary price: region=%d outputs=%d deleting=%d retained=%d new=%d gain=%d.\n",
	          GetSize(region.nodes), GetSize(region.roots), GetSize(plan.deleting), GetSize(plan.retained), GetSize(plan.needed), plan.gain);
	return plan.gain > 0;
}

bool dictionary_prove(const LutResynRegion &region, const std::map<SigBit, LutResynTable> &values,
                      const LutResynTable &care, LutResynPlan &plan) {
	int rows = 1 << GetSize(region.boundary), blocks = (rows + 63) / 64;
	int64_t work = rows * (GetSize(plan.outputs) * 2 + 1);
	for (int i : plan.needed) work += blocks * (1 << GetSize(plan.nodes[i].inputs)) * (GetSize(plan.nodes[i].inputs) + 2);
	// 已有外部函数的签名求值包含全部真实输入。
	auto signature_work = [&](LutResynRef ref) {
		work += 32;
		if (ref.node >= 0) return;
		SigBit bit = canonical(ref.bit);
		if (!bit.wire) { work += rows; return; }
		if (values.count(bit)) return;
		Cell *driver = unique_driver(bit);
		log_assert(valid_lut(driver, false));
		work += 256 + rows * (GetSize(driver->getPort(ID::A)) + 2);
	};
	for (int i : plan.needed) for (auto ref : plan.nodes[i].inputs) signature_work(ref);
	for (auto ref : plan.outputs) signature_work(ref);
	log_debug("  Dictionary proof reservation: work=%lld remaining=%lld.\n", (long long)work,
	          (long long)(resources.local_limit - resources.work - resources.commit_credit));
	if (!dictionary_charge(work, proof_work)) return false;
	vector<LutResynTable> generated(plan.nodes.size());
	auto signature = [&](LutResynRef ref) {
		if (ref.node >= 0) return generated.at(ref.node);
		SigBit bit = canonical(ref.bit);
		if (bit.wire) {
			auto found = values.find(bit);
			if (found != values.end()) return found->second;
			Cell *driver = unique_driver(bit);
			log_assert(valid_lut(driver, false));
			auto f = cell_function(driver);
			LutResynTable result;
			for (int a = 0; a < rows; a++) {
				int address = 0;
				for (int i = 0; i < GetSize(f.inputs); i++) address |= int(values.at(f.inputs[i]).get(a)) << i;
				result.set(a, f.table.get(address));
			}
			return result;
		}
		LutResynTable result;
		if (bit == State::S1) for (int a = 0; a < rows; a++) result.set(a, true);
		return result;
	};
	for (int i : plan.needed) {
		vector<LutResynTable> inputs;
		for (auto ref : plan.nodes[i].inputs) inputs.push_back(signature(ref));
		for (int a = 0; a < (1 << GetSize(inputs)); a++) if (plan.nodes[i].table.get(a))
			for (int block = 0; block < blocks; block++) {
				uint64_t product = ~uint64_t(0);
				for (int j = 0; j < GetSize(inputs); j++) product &= (a >> j) & 1 ? inputs[j].words[block] : ~inputs[j].words[block];
				generated[i].words[block] |= product;
			}
		if (rows < 64) generated[i].words[0] &= (uint64_t(1) << rows) - 1;
	}
	for (int o = 0; o < GetSize(region.roots); o++) {
		auto actual = signature(plan.outputs[o]);
		auto expected = values.at(canonical(module->cell(region.roots[o])->getPort(ID::Y)[0]));
		for (int a = 0; a < rows; a++) if (care.get(a)) log_assert(actual.get(a) == expected.get(a));
	}
	plan.proven = true; enumeration_proofs++;
	return true;
}

bool choose_dictionary_plan(const LutResynRegion &region, LutResynProof &proof, LutResynPlan &best) {
	LutResynReservation workspace(resources);
	// 字典、区域表、输出候选、联合计划及所有有限临时容器使用同一工作区。
	if (!workspace.reserve(2 * 1048576)) return false;
	int width = GetSize(region.boundary), rows = 1 << width;
	if (resources.local_limit - resources.work < 16384) return false;
	LutResynPlan capacity_plan;
	capacity_plan.deleting = region.nodes;
	for (int i = 0; i < GetSize(region.nodes); i++) capacity_plan.needed.insert(i);
	int64_t commit_allowance = dictionary_commit_work(region, capacity_plan) + 16384;
	int64_t proof_end = std::max<int64_t>(resources.work, resources.local_limit - commit_allowance);
	int64_t search_end = proof_end;
	int64_t final_reservation = std::min<int64_t>(140000,
		16384 + 4096 * GetSize(region.roots) + 1024 * GetSize(region.nodes) +
		rows * (2 * GetSize(region.roots) + 1) + (rows + 63) / 64 * 96 * std::min(16, GetSize(region.nodes)));
	search_end = std::max<int64_t>(resources.work, search_end - final_reservation);
	resources.local_limit = search_end;
	std::map<SigBit, LutResynTable> values;
	if (!dictionary_values(region, values)) return false;
	LutResynTable care;
	for (int a = 0; a < rows; a++) care.set(a, true);
	LutResynTable reachable;
	if (dictionary_environment(region, reachable)) care = reachable;
	if (resources.local_stopped || resources.stopped) return false;
	vector<DictionaryEntry> dictionary;
	vector<LutResynTable> outputs;
	for (auto root : region.roots) outputs.push_back(values.at(canonical(module->cell(root)->getPort(ID::Y)[0])));
	external_outputs += GetSize(region.roots);
	vector<int> positions;
	for (int i = 0; i < width; i++) positions.push_back(i);
	for (auto name : region.order) {
		if (!dictionary_charge(rows * (width + 1), dictionary_work)) break;
		DictionaryEntry entry;
		entry.support = positions;
		entry.table = values.at(canonical(module->cell(name)->getPort(ID::Y)[0]));
		lutresyn_reduce(entry.support, entry.table);
		if (GetSize(entry.support) <= 4) dictionary_add(dictionary, entry, width);
		entry.is_existing = true; entry.owner = name;
		entry.existing = canonical(module->cell(name)->getPort(ID::Y)[0]);
		entry.signature = values.at(entry.existing);
		dictionary_add(dictionary, std::move(entry), width);
	}
	// 已有外部函数只采用完整区域边界上的四输入函数，并证明其组合独立性。
	std::set<IdString> external;
	for (auto bit : region.boundary) {
		auto found = users.find(bit);
		if (found == users.end()) continue;
		int inspected = 0;
		for (auto name : found->second) {
			if (++inspected > options.max_neighbors) break;
			if (!dictionary_charge(8, dictionary_work)) break;
			if (!region.nodes.count(name)) external.insert(name);
		}
	}
	for (auto name : external) {
		if (!dictionary_charge(256 + rows * 5, dictionary_work)) break;
		Cell *cell = module->cell(name);
		if (!valid_lut(cell, false)) continue;
		auto f = cell_function(cell);
		DictionaryEntry entry; entry.is_existing = true; entry.owner = name;
		bool complete = true;
		for (auto bit : f.inputs) {
			auto found = std::lower_bound(region.boundary.begin(), region.boundary.end(), bit);
			if (found == region.boundary.end() || *found != bit) { complete = false; break; }
			entry.support.push_back(found - region.boundary.begin());
		}
		if (!complete || !independent(name, proof)) continue;
		entry.table = f.table; entry.signature = dictionary_expand(entry.support, f.table, width);
		entry.existing = canonical(cell->getPort(ID::Y)[0]);
		dictionary_add(dictionary, std::move(entry), width);
	}
	vector<vector<DictionaryOutput>> choices(outputs.size());
	for (auto &output_choices : choices) { DictionaryOutput preserved; preserved.kind = DictionaryOutputKind::PreserveRoot; output_choices.push_back(preserved); }
	auto offer = [&](int output, vector<int> inputs) {
		for (int input : inputs) if (input >= 0 && dictionary[input].is_existing && dictionary[input].owner == region.roots[output]) return;
		DictionaryOutput candidate;
		if (dictionary_fit(dictionary, outputs[output], care, width, std::move(inputs), candidate))
			dictionary_keep_candidate(choices[output], std::move(candidate));
	};
	// 常量、直接输入、已有 divisor 及结构 cut 属于同一完整候选池。
	vector<unsigned> output_support(outputs.size());
	vector<unsigned> function_support(dictionary.size());
	for (int d = 0; d < GetSize(dictionary); d++) for (int p : dictionary[d].support) function_support[d] |= 1u << p;
	for (int o = 0; o < GetSize(outputs); o++) {
		if (!dictionary_charge(rows * (width + 1), dictionary_work)) break;
		vector<int> support = positions; auto table = outputs[o]; lutresyn_reduce(support, table);
		vector<int> direct;
		for (int i : support) { direct.push_back(-1 - i); output_support[o] |= 1u << i; }
		offer(o, {});
		if (GetSize(direct) <= 4) offer(o, direct);
		for (int d = 0; d < GetSize(dictionary) && !resources.local_stopped; d++) {
			if (!dictionary_charge(4 + 2 * ((rows + 63) / 64), address_work)) break;
			bool same = true, inverse = true;
			for (int block = 0; block < (rows + 63) / 64; block++) {
				uint64_t differences = outputs[o].words[block] ^ dictionary[d].signature.words[block];
				same &= (differences & care.words[block]) == 0;
				inverse &= (differences & care.words[block]) == care.words[block];
			}
			if (same || inverse) offer(o, {d});
		}
	}
	// 真实结构函数先向全部输出提供各自的直接输入集合，完整拟合逐项证明。
	for (int o = 0; o < GetSize(outputs) && !resources.local_stopped; o++) {
		vector<int> ranked;
		for (int d = 0; d < GetSize(dictionary); d++) {
			if (dictionary[d].is_existing && dictionary[d].owner == region.roots[o]) continue;
			if (!function_support[d] || (function_support[d] & ~output_support[o])) continue;
			ranked.push_back(d);
		}
		if (!dictionary_charge(128 + 16 * GetSize(ranked), dictionary_work)) break;
		std::stable_sort(ranked.begin(), ranked.end(), [&](int a, int b) {
			int sa = lutresyn_count(function_support[a]), sb = lutresyn_count(function_support[b]);
			if (sa != sb) return sa > sb;
			if (dictionary[a].is_existing != dictionary[b].is_existing) return dictionary[a].is_existing;
			return a < b;
		});
		int inspected = 0;
		for (int d : ranked) {
			unsigned direct = output_support[o] & ~function_support[d];
			if (lutresyn_count(direct) > 3) continue;
			if (++inspected > 16 || resources.local_stopped) break;
			vector<int> inputs {d};
			for (int p : lutresyn_positions(direct)) inputs.push_back(-1 - p);
			offer(o, inputs);
		}
		int pairs = 0;
		for (int a = 0; a < std::min(12, GetSize(ranked)) && !resources.local_stopped && pairs < 16; a++)
			for (int b = a + 1; b < std::min(12, GetSize(ranked)) && !resources.local_stopped && pairs < 16; b++) {
				unsigned direct = output_support[o] & ~(function_support[ranked[a]] | function_support[ranked[b]]);
				if (lutresyn_count(direct) > 2) continue;
				pairs++;
				vector<int> inputs {ranked[a], ranked[b]};
				for (int p : lutresyn_positions(direct)) inputs.push_back(-1 - p);
				offer(o, inputs);
			}
	}
	vector<vector<int>> groups;
	for (int o = 0; o < GetSize(outputs); o++) groups.push_back({o});
	for (int a = 0; a < GetSize(outputs) && GetSize(groups) < GetSize(outputs) + 8; a++)
		for (int b = a + 1; b < GetSize(outputs) && GetSize(groups) < GetSize(outputs) + 8; b++)
			groups.push_back({a, b});
	for (const auto &group : groups) {
		if (resources.local_stopped || resources.stopped) break;
		if (!dictionary_charge(rows * width * GetSize(group), dictionary_work)) break;
		vector<int> support;
		for (int i = 0; i < width; i++) {
			bool relevant = false;
			for (int o : group) for (int a = 0; a < rows; a++)
				if (outputs[o].get(a) != outputs[o].get(a ^ (1 << i))) { relevant = true; break; }
			if (relevant) support.push_back(i);
		}
		if (GetSize(support) <= 4 || GetSize(support) > 7) continue;
		DictionaryProblem problem; problem.width = GetSize(support);
		for (int o : group) {
			LutResynTable table;
			for (int a = 0; a < (1 << GetSize(support)); a++) table.set(a, outputs[o].get(lutresyn_deposit(a, support)));
			if (table.get(0)) for (int a = 0; a < (1 << GetSize(support)); a++) table.set(a, !table.get(a));
			problem.value.push_back(table);
		}
		std::sort(problem.value.begin(), problem.value.end());
		problem.value.erase(std::unique(problem.value.begin(), problem.value.end()), problem.value.end());
		for (int a = 0; a < rows; a++) if (care.get(a)) problem.care.set(lutresyn_project(a, support), true);
		auto cached = dictionary_problem_cache.find(problem);
		vector<DictionarySeed> generated;
		const vector<DictionarySeed> *seeds = nullptr;
		if (cached == dictionary_problem_cache.end()) {
			// 抽象分解使用有限子额度，留存已完成的真实种子供候选构造。
			int64_t old_limit = resources.local_limit;
			resources.local_limit = std::min<int64_t>(old_limit, resources.work + 24000);
			bool complete = dictionary_decompose(problem, generated);
			resources.local_limit = old_limit; resources.local_stopped = false;
			seeds = &generated;
			int64_t bytes = 1024 + 768 * generated.capacity();
			while (complete && !dictionary_problem_cache.empty() &&
			       (GetSize(dictionary_problem_cache) >= options.max_problems || problem_memory + bytes > 4 * 1048576)) {
				auto expired = dictionary_problem_cache.begin();
				if (!dictionary_charge(32 + 8 * GetSize(expired->second.seeds), dictionary_work)) break;
				resources.release(expired->second.bytes); problem_memory -= expired->second.bytes;
				dictionary_problem_cache.erase(expired);
			}
			if (complete && GetSize(dictionary_problem_cache) < options.max_problems &&
			    problem_memory + bytes <= 4 * 1048576 && bytes <= resources.memory_limit - resources.memory && resources.reserve(bytes)) {
				problem_memory += bytes;
				cached = dictionary_problem_cache.emplace(std::move(problem), DictionaryCachedProblem {generated, bytes}).first;
				seeds = &cached->second.seeds;
			}
		} else { problem_hits++; seeds = &cached->second.seeds; }
		std::set<vector<int>> input_sets;
		for (const auto &seed : *seeds) {
			if (resources.local_stopped || resources.stopped) break;
			vector<int> inputs;
			bool complete = true;
			for (int i = 0; i < GetSize(seed.tables); i++) {
				DictionaryEntry entry; entry.table = seed.tables[i];
				for (int p : lutresyn_positions(seed.bound[i])) entry.support.push_back(support[p]);
				int index = dictionary_add(dictionary, std::move(entry), width);
				if (index < 0) { complete = false; break; }
				inputs.push_back(index);
			}
			if (!complete) continue;
			for (int p : lutresyn_positions(seed.top)) inputs.push_back(-1 - support[p]);
			std::sort(inputs.begin(), inputs.end());
			if (!dictionary_charge(32 + 8 * GetSize(input_sets), dictionary_work)) break;
			if (!input_sets.insert(inputs).second) continue;
			for (int o : group) offer(o, inputs);
			vector<vector<int>> substitutions {inputs};
			for (int token : inputs) if (token >= 0 && !dictionary[token].is_existing) {
				int initial = GetSize(substitutions);
				for (int d = 0; d < GetSize(dictionary); d++) if (dictionary[d].is_existing) {
					if (!dictionary_charge((rows + 63) / 64 * 2 + 4, dictionary_work)) break;
					bool same = true, inverse = true;
					for (int block = 0; block < (rows + 63) / 64; block++) {
						uint64_t left = dictionary[token].signature.words[block], right = dictionary[d].signature.words[block];
						uint64_t valid = rows < 64 ? (uint64_t(1) << rows) - 1 : ~uint64_t(0);
						same &= left == right; inverse &= (left ^ right) == valid;
					}
					if (!same && !inverse) continue;
					for (int i = 0; i < initial && GetSize(substitutions) < 8; i++) {
						vector<int> replaced = substitutions[i];
						std::replace(replaced.begin(), replaced.end(), token, d);
						for (int o : group) offer(o, replaced);
						substitutions.push_back(std::move(replaced));
					}
				}
			}
			if (GetSize(seed.tables) == 1) single_bridge_plans++; else two_bridge_plans++;
		}
	}
	// 每个输出使用自己的共享子集，地址冲突以相同 care 域完整检查。
	for (int o = 0; o < GetSize(outputs) && !resources.local_stopped; o++) {
		vector<int> pool;
		for (int d = 0; d < GetSize(dictionary); d++) pool.push_back(d);
		for (int i = 0; i < width; i++) pool.push_back(-1 - i);
		vector<vector<int>> beam(1);
		for (int depth = 1; depth <= 4 && !resources.local_stopped; depth++) {
			vector<std::pair<int, vector<int>>> next;
			for (const auto &prefix : beam) for (int token : pool) {
				if (!prefix.empty() && token <= prefix.back()) continue;
				if (token >= 0 && dictionary[token].is_existing && dictionary[token].owner == region.roots[o]) continue;
				vector<int> inputs = prefix; inputs.push_back(token);
				DictionaryOutput candidate;
				if (dictionary_fit(dictionary, outputs[o], care, width, inputs, candidate)) {
					dictionary_keep_candidate(choices[o], std::move(candidate)); continue;
				}
				if (resources.local_stopped) break;
				if (!dictionary_charge(rows * (depth + 2), address_work)) break;
				int seen[16][2] = {}; int conflicts = 0;
				for (int a = 0; a < rows; a++) if (care.get(a)) {
					int address = 0;
					for (int i = 0; i < GetSize(inputs); i++) {
						int input = inputs[i];
						address |= int(input < 0 ? (a >> (-1 - input)) & 1 : dictionary[input].signature.get(a)) << i;
					}
					seen[address][outputs[o].get(a)]++;
				}
				for (int a = 0; a < (1 << depth); a++) conflicts += std::min(seen[a][0], seen[a][1]);
				next.emplace_back(conflicts, std::move(inputs));
			}
			int levels = 1;
			for (size_t count = next.size(); count > 1; count >>= 1) levels++;
			if (!dictionary_charge(int64_t(next.size()) * levels * 6, address_work)) break;
			std::sort(next.begin(), next.end());
			beam.clear();
			for (int i = 0; i < std::min(8, GetSize(next)); i++) beam.push_back(std::move(next[i].second));
		}
	}
	// 留存的全部候选已经完成局部证明；联合价格与证明使用预留额度。
	resources.local_stopped = false;
	resources.local_limit = proof_end;
	if (!dictionary_charge(32 * GetSize(region.nodes) * GetSize(region.nodes), price_work)) return false;
	std::map<IdString, std::set<IdString>> closures;
	for (auto name : region.order) {
		closures[name].insert(name);
		for (auto bit : cell_inputs.at(name)) {
			Cell *driver = unique_driver(bit);
			if (driver && region.nodes.count(driver->name)) closures[name].insert(closures[driver->name].begin(), closures[driver->name].end());
		}
	}
	vector<int> output_order;
	if (ys_debug(1)) {
		log_debug("  Dictionary region: cells=%d inputs=%d outputs=%d.\n", GetSize(region.nodes), width, GetSize(outputs));
		for (int o = 0; o < GetSize(outputs); o++) {
			log_debug("    output %s choices=%d retained_closure=%d.\n", log_id(region.roots[o]), GetSize(choices[o]), GetSize(closures[region.roots[o]]));
			for (const auto &choice : choices[o]) {
				log_debug("      %s", choice.kind == DictionaryOutputKind::PreserveRoot ? "PreserveRoot" : "Rebuild");
				for (int token : choice.inputs) log_debug(" %s%d", token >= 0 ? "G" : "x", token >= 0 ? token : -1 - token);
				log_debug("\n");
			}
		}
	}
	for (int o = 0; o < GetSize(outputs); o++) output_order.push_back(o);
	std::stable_sort(output_order.begin(), output_order.end(), [&](int a, int b) { return choices[a].size() < choices[b].size(); });
	vector<DictionaryPartial> beam(1);
	beam[0].outputs.resize(outputs.size());
	for (int o : output_order) {
		vector<DictionaryPartial> next;
		for (const auto &partial : beam) for (const auto &candidate : choices[o]) {
			if (!dictionary_charge(32 + 16 * (GetSize(partial.functions) + GetSize(candidate.functions)), price_work)) break;
			DictionaryPartial merged = partial;
			merged.outputs[o] = candidate;
			merged.functions.insert(candidate.functions.begin(), candidate.functions.end());
			if (candidate.kind == DictionaryOutputKind::PreserveRoot) merged.retained.insert(closures[region.roots[o]].begin(), closures[region.roots[o]].end());
			for (int d : candidate.functions) if (dictionary[d].is_existing && region.nodes.count(dictionary[d].owner))
				merged.retained.insert(closures[dictionary[d].owner].begin(), closures[dictionary[d].owner].end());
			merged.estimate = 0;
			for (int d : merged.functions) if (!dictionary[d].is_existing && GetSize(dictionary[d].support) > 1) merged.estimate++;
			for (int i = 0; i < GetSize(merged.outputs); i++) {
				const auto &output = merged.outputs[i];
				if (output.kind == DictionaryOutputKind::Rebuild && (GetSize(output.inputs) > 1 || (GetSize(output.inputs) == 1 && output.table.get(0)))) merged.estimate++;
			}
			merged.estimate += GetSize(merged.retained);
			next.push_back(std::move(merged));
		}
		int levels = 1, maximum_functions = 0;
		for (size_t count = next.size(); count > 1; count >>= 1) levels++;
		for (const auto &candidate : next) maximum_functions = std::max(maximum_functions, GetSize(candidate.functions));
		if (!dictionary_charge(int64_t(next.size()) * levels * (maximum_functions + 4), price_work)) return false;
		std::stable_sort(next.begin(), next.end(), [](const DictionaryPartial &a, const DictionaryPartial &b) {
			if (a.estimate != b.estimate) return a.estimate < b.estimate;
			return a.functions < b.functions;
		});
		if (GetSize(next) > 8) next.resize(8);
		beam = std::move(next);
		if (beam.empty() || resources.local_stopped || resources.stopped) return false;
	}
	int best_gain = 0;
	for (const auto &partial : beam) {
		if (resources.local_stopped || resources.stopped) break;
		if (root_complete_plans >= 32) { resources.local_stopped = true; break; }
		LutResynPlan plan;
		std::map<int, LutResynRef> references;
		for (int d : partial.functions) {
			const auto &entry = dictionary[d];
			if (entry.is_existing) references.emplace(d, LutResynRef(entry.existing));
			else {
				vector<LutResynRef> inputs;
				for (int i : entry.support) inputs.emplace_back(region.boundary[i]);
				auto ref = synthesize(plan, inputs, entry.table, proof, workspace);
				if (!ref) break;
				references.emplace(d, *ref);
			}
		}
		if (GetSize(references) != GetSize(partial.functions)) break;
		for (int o = 0; o < GetSize(partial.outputs); o++) {
			const auto &output = partial.outputs[o];
			plan.preserve.push_back(output.kind == DictionaryOutputKind::PreserveRoot);
			if (output.kind == DictionaryOutputKind::PreserveRoot) {
				plan.outputs.emplace_back(canonical(module->cell(region.roots[o])->getPort(ID::Y)[0])); continue;
			}
			vector<LutResynRef> inputs;
			for (int token : output.inputs) inputs.push_back(token < 0 ? LutResynRef(region.boundary[-1 - token]) : references.at(token));
			auto ref = synthesize(plan, inputs, output.table, proof, workspace);
			if (!ref) break;
			plan.outputs.push_back(*ref);
		}
		if (GetSize(plan.outputs) != GetSize(outputs)) break;
		complete_joint_plans++; root_complete_plans++;
		if (!dictionary_price(region, plan) || !dictionary_prove(region, values, care, plan)) continue;
		if (plan.gain > best_gain || (plan.gain == best_gain && plan.needed.size() < best.needed.size())) {
			best_gain = plan.gain; best = std::move(plan);
		}
	}
	resources.local_limit = std::min<int64_t>(resources.work_limit, root_work_end);
	return best_gain > 0;
}

int64_t root_work_end = 0;
int root_complete_plans = 0;

int64_t dictionary_commit_work(const LutResynRegion &region, const LutResynPlan &plan) const {
	int64_t amount = 512 + 64 * GetSize(plan.deleting) + 192 * GetSize(plan.needed) + 64 * GetSize(region.roots);
	std::set<IdString> affected;
	for (auto root : region.roots) {
		auto found = users.find(canonical(module->cell(root)->getPort(ID::Y)[0]));
		if (found != users.end()) affected.insert(found->second.begin(), found->second.end());
	}
	for (auto name : plan.deleting) affected.insert(name);
	for (auto name : affected) amount += 32 + 32 * (GetSize(cell_inputs.at(name)) + GetSize(cell_outputs.at(name)));
	amount += 32 * GetSize(region_cache) + 32 * GetSize(cut_cache);
	for (const auto &entry : region_cache) amount += 8 * GetSize(entry.second.region.nodes);
	for (const auto &entry : cut_cache) for (const auto &cut : entry.second) amount += 8 * GetSize(cut.nodes);
	return amount;
}

std::deque<IdString> dictionary_root_queue() {
	struct RankedRoot { IdString name; int64_t score, estimate; };
	vector<RankedRoot> ranked;
	int levels = 1;
	for (size_t count = pending.size(); count > 1; count >>= 1) levels++;
	int64_t sorting = 4 * int64_t(pending.size()) * levels;
	int64_t allowance = resources.work_limit / 10;
	if (sorting > allowance) return {};
	int64_t start = resources.work;
	for (auto name : pending) {
		int64_t score = 0, estimate = 1;
		if (resources.work - start + sorting + 128 < allowance) {
			std::set<IdString> cone;
			std::set<SigBit> boundary;
			vector<IdString> queue {name};
			int reuse = 0;
			while (!queue.empty() && GetSize(cone) < 32 && resources.work - start + sorting + 128 < allowance) {
				IdString current = queue.back(); queue.pop_back();
				if (!cone.insert(current).second) continue;
				if (!dictionary_charge(64, sorting_work)) return {};
				for (auto bit : cell_inputs.at(current)) {
					Cell *driver = unique_driver(bit);
					if (valid_lut(driver, true)) queue.push_back(driver->name);
					else boundary.insert(bit);
					auto found = users.find(bit);
					if (found != users.end()) reuse += std::min(options.max_neighbors, GetSize(found->second));
				}
			}
			int width = std::min(10, GetSize(boundary));
			score = std::max(1, GetSize(cone) - 1) * 64 + reuse;
			estimate = 16 + (1 << width) * std::max(1, GetSize(cone));
		}
		ranked.push_back({name, score, estimate});
	}
	if (!dictionary_charge(sorting, sorting_work)) return {};
	std::sort(ranked.begin(), ranked.end(), [](const RankedRoot &a, const RankedRoot &b) {
		int64_t left = a.score * b.estimate, right = b.score * a.estimate;
		if (left != right) return left > right;
		return a.name < b.name;
	});
	std::deque<IdString> queue;
	for (const auto &root : ranked) queue.push_back(root.name);
	return queue;
}
