#ifndef YOSYS_OPT_LUT4_FEEDBACK_H
#define YOSYS_OPT_LUT4_FEEDBACK_H

#include "opt_lut4_mapping.h"

YOSYS_NAMESPACE_BEGIN
namespace Lut4Mapping {

enum class FeedbackStatus { Prepared, Unsupported, LimitReached };
struct FeedbackResult {
	FeedbackStatus status;
	std::string reason;
	int64_t luts = 0, expansion = 0, work = 0;
};

struct FeedbackResources {
	std::function<bool(int64_t)> spend;
	std::function<bool(int64_t, int64_t)> reserve;
	std::function<void()> observe;
	std::function<bool()> available;
};

inline int64_t feedback_scan_work(Design *design) {
	int64_t result = 64;
	for (auto module : design->selected_unboxed_modules()) {
		result = capacity_add(result, capacity_add(capacity_mul(8, module->cells_size()), capacity_mul(4, module->wires_size())));
		for (auto wire : module->wires()) result = capacity_add(result, wire->width);
		for (auto cell : module->cells()) for (auto &port : cell->connections()) result = capacity_add(result, capacity_add(4, GetSize(port.second)));
		for (auto &connection : module->connections()) result = capacity_add(result, capacity_add(4, capacity_add(GetSize(connection.first), GetSize(connection.second))));
	}
	return result;
}

inline int64_t feedback_index_capacity(Design *design) {
	int64_t result = 1024;
	for (auto module : design->selected_unboxed_modules()) result = capacity_add(result, capacity_mul(2, post_index_bytes(module, true)));
	return result;
}

// 保存名称和原属性，模块重建后仍通过当前 Design 查询对象。
struct FeedbackBoundaryGuard {
	struct Attribute { IdString module, name; bool wire, present; Const value; };
	Design *design;
	std::vector<Attribute> saved;
	explicit FeedbackBoundaryGuard(Design *design) : design(design) {
		for (auto module : design->selected_unboxed_modules()) {
			pool<IdString> wires;
			for (auto cell : module->cells()) if (boundary(cell, design)) {
				auto keep = cell->attributes.find(ID::keep);
				saved.push_back({module->name, cell->name, false, keep != cell->attributes.end(), keep == cell->attributes.end() ? Const() : keep->second});
				cell->set_bool_attribute(ID::keep);
				for (auto &port : cell->connections()) for (auto bit : port.second) if (bit.wire) wires.insert(bit.wire->name);
			}
			for (auto wire : module->wires())
				if (wire->port_id || wire->get_bool_attribute(ID::keep) || wire->has_attribute(ID::init) || user_boundary_attributes(wire->attributes)) wires.insert(wire->name);
			for (auto name : wires) {
				auto wire = module->wire(name);
				auto keep = wire->attributes.find(ID::keep);
				saved.push_back({module->name, name, true, keep != wire->attributes.end(), keep == wire->attributes.end() ? Const() : keep->second});
				wire->set_bool_attribute(ID::keep);
			}
		}
	}
	void restore() {
		for (auto &item : saved) {
			auto module = design->module(item.module);
			if (!module) log_error("opt_lut4_feedback: protected module %s disappeared.\n", item.module);
			auto wire = item.wire ? module->wire(item.name) : nullptr;
			auto cell = item.wire ? nullptr : module->cell(item.name);
			if (!wire && !cell) log_error("opt_lut4_feedback: protected object %s.%s disappeared.\n", item.module, item.name);
			auto &attributes = item.wire ? wire->attributes : cell->attributes;
			if (item.present) attributes[ID::keep] = item.value;
			else attributes.erase(ID::keep);
		}
		saved.clear();
	}
	~FeedbackBoundaryGuard() { restore(); }
};

inline FeedbackResult prepare_feedback(Design *design, FeedbackResources &resources) {
	StateGuard state(design);
	FeedbackResult result {FeedbackStatus::Prepared, "fixed Boolean preparation completed"};
	auto charge = [&](int64_t work) {
		if (!resources.available() || !resources.spend(work)) { result.status = FeedbackStatus::LimitReached; result.reason = "preparation work or deadline allowance"; return false; }
		result.work = capacity_add(result.work, work); return true;
	};
	auto reserve = [&](int64_t growth) {
		if (!resources.available() || !resources.reserve(growth, feedback_index_capacity(design))) {
			result.status = FeedbackStatus::LimitReached; result.reason = "preparation capacity or deadline allowance"; return false;
		}
		return true;
	};
	if (!reserve(0) || !charge(feedback_scan_work(design))) return result;
	CellTypes types(design);
	RTLIL::Selection luts(false);
	for (auto module : design->selected_unboxed_modules()) {
		if (!design->selected_whole_module(module) || module->has_processes() || module->has_memories())
			log_error("opt_lut4_feedback: incomplete generic module %s.\n", module);
		SigMap sigmap(module);
		pool<SigBit> protected_outputs;
		dict<SigBit, int> drivers;
		for (auto wire : module->wires()) {
			if (wire->get_bool_attribute(ID::keep) || wire->has_attribute(ID::init) || user_boundary_attributes(wire->attributes))
				for (auto bit : sigmap(wire)) protected_outputs.insert(bit);
			if (wire->port_input) for (auto bit : sigmap(wire)) drivers[bit]++;
		}
		for (auto cell : module->cells()) for (auto &port : cell->connections())
			if (types.cell_output(cell->type, port.first)) for (auto bit : sigmap(port.second)) drivers[bit]++;
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux))) {
				result.status = FeedbackStatus::Unsupported; result.reason = "generic checkpoint contains an existing mux boundary"; return result;
			}
			if (cell->type != ID($lut) || cell->has_keep_attr()) continue;
			if (!cell->parameters.count(ID::WIDTH) || !cell->parameters.count(ID::LUT) || !cell->hasPort(ID::A) || !cell->hasPort(ID::Y) ||
				cell->parameters.size() != 2 || cell->connections().size() != 2 || !cell->getParam(ID::WIDTH).is_fully_def())
				log_error("opt_lut4_feedback: invalid generic LUT fields in %s.%s.\n", module, cell);
			auto width_value = cell->getParam(ID::WIDTH).try_as_int();
			if (!width_value || *width_value < 0 || *width_value > 4)
				log_error("opt_lut4_feedback: invalid generic LUT width in %s.%s.\n", module, cell);
			int width = *width_value;
			if (GetSize(cell->getPort(ID::A)) != width || GetSize(cell->getPort(ID::Y)) != 1 || GetSize(cell->getParam(ID::LUT)) != (1 << width))
				log_error("opt_lut4_feedback: invalid generic LUT dimensions in %s.%s.\n", module, cell);
			auto output = sigmap(cell->getPort(ID::Y)).as_bit();
			bool safe = output.wire && drivers[output] == 1 && !protected_outputs.count(output) && cell->getParam(ID::LUT).is_fully_def();
			for (auto bit : sigmap(cell->getPort(ID::A))) if (!bit.wire && bit.data != State::S0 && bit.data != State::S1) safe = false;
			for (auto &attribute : cell->attributes) if (attribute.first != ID::src && attribute.first != ID::keep) safe = false;
			if (!safe) {
				result.status = FeedbackStatus::Unsupported;
				result.reason = stringf("ordinary LUT %s.%s has protected, unknown, attributed or nonunique signals", log_id(module), log_id(cell));
				return result;
			}
			luts.select(module, cell); result.luts++;
			result.expansion = capacity_add(result.expansion, (1 << width) - 1);
		}
	}
	if (!result.luts) { result.status = FeedbackStatus::Unsupported; result.reason = "generic checkpoint has no ordinary LUT"; return result; }
	// 每个递归节点包含一位 mux、至多一条中间 wire、端口/参数容器及临时索引。
	int64_t expansion_capacity = capacity_mul(result.expansion, sizeof(Cell) + sizeof(Wire) + 1536);
	if (!reserve(expansion_capacity)) return result;
	FeedbackBoundaryGuard boundaries(design);
	auto selection = [&]() {
		RTLIL::Selection current(false);
		for (auto module : design->selected_unboxed_modules()) for (auto cell : module->cells())
			if (!boundary(cell, design)) current.select(module, cell);
		return current;
	};
	auto command = [&](const char *name, bool whole = false) {
		if (!reserve(0) || !charge(feedback_scan_work(design))) return false;
		auto started = std::chrono::steady_clock::now();
		if (whole) Pass::call(design, name);
		else Pass::call_on_selection(design, selection(), name);
		resources.observe();
		log("opt_lut4_feedback: preparation command=%s scan proxy=%lld elapsed seconds=%.9f.\n", name,
			(long long)result.work, std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count());
		if (!resources.available()) { result.status = FeedbackStatus::LimitReached; result.reason = "preparation deadline allowance"; return false; }
		return true;
	};
	if (!charge(feedback_scan_work(design))) return result;
	auto normalization_started = std::chrono::steady_clock::now();
	Pass::call_on_selection(design, luts, "opt_lut_ins"); resources.observe();
	log("opt_lut4_feedback: preparation command=opt_lut_ins elapsed seconds=%.9f.\n",
		std::chrono::duration<double>(std::chrono::steady_clock::now() - normalization_started).count());
	RTLIL::Selection expanded(false);
	result.expansion = 0;
	for (auto module : design->selected_unboxed_modules()) for (auto cell : module->cells().to_vector()) {
		if (cell->type != ID($lut) || cell->has_keep_attr()) continue;
		if (!cell->getParam(ID::WIDTH).as_int()) {
			module->connect(cell->getPort(ID::Y), cell->getParam(ID::LUT)[0]); module->remove(cell);
		} else {
			expanded.select(module, cell);
			result.expansion = capacity_add(result.expansion, (1 << cell->getParam(ID::WIDTH).as_int()) - 1);
		}
	}
	expansion_capacity = capacity_mul(result.expansion, sizeof(Cell) + sizeof(Wire) + 1536);
	if (!reserve(expansion_capacity) || !charge(capacity_add(feedback_scan_work(design), capacity_mul(result.expansion, 8)))) return result;
	auto expansion_started = std::chrono::steady_clock::now();
	Pass::call_on_selection(design, expanded, "lut2mux -word"); resources.observe();
	log("opt_lut4_feedback: preparation command=lut2mux -word expansion E=%lld elapsed seconds=%.9f.\n",
		(long long)result.expansion, std::chrono::duration<double>(std::chrono::steady_clock::now() - expansion_started).count());
	if (!command("opt_expr -full -keepdc -noclkinv") || !command("opt_merge -nomux -keepdc")) return result;
	for (int round = 0; round < 2; ++round)
		if (!command("opt_muxtree", true) || !command("opt_reduce -full") || !command("opt_merge -keepdc") ||
			!command("opt_share") || !command("opt_clean", true) || !command("opt_expr -full -keepdc -noclkinv")) return result;
	if (!command("simplemap") || !command("opt_expr -fine -keepdc -noclkinv") || !command("opt_merge -keepdc") || !command("opt_clean", true)) return result;
	if (!reserve(0) || !charge(capacity_mul(2, feedback_scan_work(design)))) return result;
	boundaries.restore();
	for (auto module : design->selected_unboxed_modules()) for (auto cell : module->cells())
		if (cell->type == ID($lut) && !cell->has_keep_attr()) log_error("opt_lut4_feedback: ordinary LUT remains in %s.%s.\n", module, cell);
	log("opt_lut4_feedback: prepared generation=1 ordinary LUTs=%lld expansion E=%lld total preparation proxy=%lld.\n",
		(long long)result.luts, (long long)result.expansion, (long long)result.work);
	return result;
}

}
YOSYS_NAMESPACE_END
#endif
