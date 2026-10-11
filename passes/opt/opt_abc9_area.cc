#include "opt_lut4_mapping.h"

#include <charconv>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static int abc9_area_integer(const std::string &value, int low, int high)
{
	int result = 0;
	auto parsed = std::from_chars(value.data(), value.data() + value.size(), result);
	if (parsed.ec != std::errc() || parsed.ptr != value.data() + value.size() || result < low || result > high)
		log_cmd_error("opt_abc9_area: expected an integer in [%d, %d], got '%s'.\n", low, high, value);
	return result;
}

struct OptAbc9AreaPass : Pass
{
	OptAbc9AreaPass() : Pass("opt_abc9_area", "select a bounded ABC9 LUT4 area mapping") {}
	void help() override
	{
		log("\n    opt_abc9_area [options] [selection]\n\n");
		log("Map fully selected unmapped modules using independent complete Designs.\n");
		log("ABC9 handles FF, memory, keep and technology boundaries. All candidates\n");
		log("start with the same original Design, including complete library dependencies.\n");
		log("Choose $lut (WIDTH <= 4) plus inverter output bits, retaining earlier ties.\n\n");
		log("    -candidates <1..3>  fixed-order candidate count (default: 3)\n");
		log("    -W <0..1000000>     LUT wire delay in ps (default: 300)\n");
		log("    -exe <command>      ABC executable (default: ABC9's executable)\n\n");
		log("    -script-family <area-lutpack|cascade-area|rewrite-refactor|expanded-cuts|feedback-boolean>\n");
		log("        execute one selected script family\n\n");
		log("Order: area-lutpack; cascade-area; rewrite-refactor. All scripts use dch\n");
		log("with 4 simulation words, 100 SAT conflicts and 1000 variables, and one\n");
		log("LUT packing sweep. Cascade-area uses N4/Q3/S2/L10 with zero-cost\n");
		log("replacements, support <= 13, and mfs2 before and after LUT packing\n");
		log("with W=1 F=8 D=64 M=64 C=500 L=10. Area-lutpack and rewrite-refactor\n");
		log("use support <= 10, cuts 8 and 12, F=1 A=2, and mfs2\n");
		log("W=1 F=8 D=20 M=64 C=500 L=0. Expanded-cuts is available explicitly,\n");
		log("with cuts 16 (12 above 20000 pre-ABC cells); it uses two\n");
		log("area-flow and three exact-area rounds, mfs2 area resubstitution with\n");
		log("W=2 F=12 D=64 M=96 C=750 L=0 and support <= 10.\n");
		log("Rewrite-refactor includes two rewrite, two balance and one refactor sweep.\n");
		log("Feedback-boolean executes resyn2 and two bounded resub sweeps, then one\n");
		log("if/C8/F1/A2 mapping, lutpack/N3/Q1/S2/L10 and mfs2/W1/F8/D64/M64/L10/C500.\n");
		log("Run proc/memory/techmap before mapping selected active modules.\n");
		log("ABC9 verification is mandatory. Caller configuration and saved designs survive.\n\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		Lut4Mapping::StateGuard state(design);
		int candidates = 3, wire_delay = 300;
		bool single = false;
		std::string family, executable = design->scratchpad_get_string("abc9.exe");
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-candidates" && argidx + 1 < args.size()) candidates = abc9_area_integer(args[++argidx], 1, 3);
			else if (args[argidx] == "-W" && argidx + 1 < args.size()) wire_delay = abc9_area_integer(args[++argidx], 0, 1000000);
			else if (args[argidx] == "-exe" && argidx + 1 < args.size()) executable = args[++argidx];
			else if (args[argidx] == "-single-map") single = true;
			else if (args[argidx] == "-script-family" && argidx + 1 < args.size()) family = args[++argidx];
			else break;
		}
		extra_args(args, argidx, design);
		log_header(design, "Executing OPT_ABC9_AREA pass.\n");
		for (auto module : design->selected_modules())
			if (!design->selected_whole_module(module)) log_cmd_error("opt_abc9_area: module %s is partially selected.\n", module);
		if (single) {
			// opt_lut4_mapping.evaluating 与 opt_fsm_lut4.evaluating 在完整映射入口恒同置、在 clear_products/出口恒同清（见 opt_fsm_lut4.cc），查其一即可。
			if (!design->scratchpad_get_bool("opt_lut4_mapping.evaluating") || family.empty())
				log_cmd_error("opt_abc9_area: single-map requires an internal complete mapping candidate.\n");
			Lut4Mapping::map_one(design, Lut4Mapping::parse_script_kind(family), wire_delay, executable);
			return;
		}
		if (!family.empty()) candidates = 1;
		std::unique_ptr<Design> best;
		Lut4Mapping::Metrics best_cost;
		Lut4Mapping::ScriptKind best_kind = Lut4Mapping::ScriptKind::AreaLutpack;
		std::array<Lut4Mapping::ScriptKind, 3> scripts {{Lut4Mapping::ScriptKind::AreaLutpack, Lut4Mapping::ScriptKind::CascadeArea, Lut4Mapping::ScriptKind::RewriteRefactor}};
		if (!family.empty()) scripts[0] = Lut4Mapping::parse_script_kind(family);
		for (int index = 0; index < candidates; index++) {
			auto start = std::chrono::steady_clock::now();
			auto candidate = Lut4Mapping::clone_design(design);
			Lut4Mapping::map_one(candidate.get(), scripts[index], wire_delay, executable);
			auto cost = Lut4Mapping::metrics(candidate.get());
			double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
			log("opt_abc9_area: candidate=%s lut=%lld not=%lld area=%lld seconds=%.6f\n", Lut4Mapping::script_name(scripts[index]),
				(long long)cost.luts, (long long)cost.inverters, (long long)cost.area(), elapsed);
			if (!best || cost.area() < best_cost.area()) { best = std::move(candidate); best_cost = cost; best_kind = scripts[index]; }
		}
		log("opt_abc9_area: selected candidate=%s area=%lld candidates=%d\n", Lut4Mapping::script_name(best_kind), (long long)best_cost.area(), candidates);
		Pass::call(best.get(), "check -assert");
		Lut4Mapping::transfer(design, best.get());
	}
} OptAbc9AreaPass;

PRIVATE_NAMESPACE_END
