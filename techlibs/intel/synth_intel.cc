/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2024  Richard Herveille <richard.herveille@roalogic.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "passes/opt/opt_lut4_mapping.h"
#include "passes/opt/muxledger.h"
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthIntelPass : public ScriptPass {
	SynthIntelPass() : ScriptPass("synth_intel", "synthesis for Intel (Altera) FPGAs.")
	{
		reset_flags();
		block_active = false;
		help_mode = false;
		active_design = nullptr;
		experimental();
	}

	string top_opt, family_opt, vout_file, blif_file;
	bool flatten, nobram, dff, nodsp, iopads;
	bool fsm_lut4_eval = false, fsm_lut4_enabled = false, native_carry = true;
	bool lut_feedback = false;
	unsigned invocation_depth = 0;

	using SavedState = std::tuple<string, string, string, string, bool, bool, bool, bool, bool,
		bool, bool, bool, bool, bool, bool, RTLIL::Design *, string, string>;
	struct Invocation {
		SynthIntelPass &pass;
		SavedState saved;
		Invocation(SynthIntelPass &pass) : pass(pass), saved(pass.top_opt, pass.family_opt, pass.vout_file,
			pass.blif_file, pass.flatten, pass.nobram, pass.dff, pass.nodsp, pass.iopads,
			pass.fsm_lut4_eval, pass.fsm_lut4_enabled, pass.native_carry, pass.lut_feedback, pass.block_active, pass.help_mode,
			pass.active_design, pass.active_run_from, pass.active_run_to)
		{
			++pass.invocation_depth;
		}
		~Invocation()
		{
			std::tie(pass.top_opt, pass.family_opt, pass.vout_file, pass.blif_file, pass.flatten,
				pass.nobram, pass.dff, pass.nodsp, pass.iopads, pass.fsm_lut4_eval,
				pass.fsm_lut4_enabled, pass.native_carry, pass.lut_feedback, pass.block_active, pass.help_mode, pass.active_design,
				pass.active_run_from, pass.active_run_to) = std::move(saved);
			--pass.invocation_depth;
		}
	};

	struct MuxInferSatBudget {
		RTLIL::Design *design;
		bool temporary;
		explicit MuxInferSatBudget(RTLIL::Design *design) : design(design),
			temporary(design && !design->scratchpad.count("opt_muxinfer.sat_effort"))
		{
			if (!temporary)
				return;
			constexpr int64_t base = 100000, scale = 256, maximum = 2000000;
			constexpr int64_t occurrence_limit = (maximum - base + scale - 1) / scale;
			int64_t occurrences = 0;
			// 饱和累计实际端口输入出现次数，保证预算计算不会溢出。
			for (auto module : design->selected_modules())
				for (auto cell : module->selected_cells())
					if (cell->type.in(ID($mux), ID($pmux)))
						for (auto port : {ID::A, ID::B, ID::S})
							occurrences += std::min<int64_t>(occurrence_limit - occurrences, GetSize(cell->getPort(port)));
			design->scratchpad_set_int("opt_muxinfer.sat_effort", std::min<int64_t>(maximum, base + scale * occurrences));
		}
		~MuxInferSatBudget()
		{
			if (temporary)
				design->scratchpad_unset("opt_muxinfer.sat_effort");
		}
	};

	void help() override
	{
		Invocation invocation(*this);
		reset_flags();
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_intel [options]\n");
		log("\n");
		log("This command runs synthesis for Intel FPGAs.\n");
		log("\n");
		log("    -family <max10 | cyclone10lp | cycloneiv | cycloneive>\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        MAX10 is the default target if no family argument specified.\n");
		log("        For Cyclone IV GX devices, use cycloneiv argument; for Cyclone IV E, use\n");
		log("        cycloneive. For Cyclone V and Cyclone 10 GX, use the synth_intel_alm\n");
		log("        backend instead.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -vqm <file>\n");
		log("        write the design to the specified Verilog Quartus Mapping File. Writing\n");
		log("        of an output file is omitted if this parameter is not specified.\n");
		log("        Note that this backend has not been tested and is likely incompatible\n");
		log("        with recent versions of Quartus.\n");
		log("\n");
		log("    -vpr <file>\n");
		log("        write BLIF files for VPR flow experiments. The synthesized BLIF output\n");
		log("        file is not compatible with the Quartus flow. Writing of an\n");
		log("        output file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -dff\n");
		log("        pass DFFs to ABC to perform sequential logic optimisations\n");
		log("        (EXPERIMENTAL)\n");
		log("\n");
		log("    -iopads\n");
		log("        use IO pad cells in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to MUL18/MUL9 cells\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -lut-feedback\n");
		log("        enable one generation of generic LUT feedback in the complete\n");
		log("        Cyclone IV combinational mapping search (disabled by default).\n");
		log("        Requires -family cycloneiv, without -dff or -run. Feedback shares\n");
		log("        the four complete mapping slots and all search resource limits.\n");
		log("\n");
		log("For cycloneiv, the coarse opt_muxinfer SAT budget per module defaults to\n");
		log("min(2000000, 100000 + 256 * N), where N counts input bit occurrences on\n");
		log("the A, B and S ports of selected $mux/$pmux cells in the design. An explicit\n");
		log("opt_muxinfer.sat_effort scratchpad value is preserved, including 0 (unlimited).\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	void clear_flags() override
	{
		// Pass::pre_execute 在 execute 之前调用此方法；重入期间保留外层状态。
		if (invocation_depth == 0)
			reset_flags();
	}

	void reset_flags()
	{
		top_opt = "-auto-top";
		family_opt = "max10";
		vout_file = "";
		blif_file = "";
		flatten = true;
		nobram = false;
		dff = false;
		nodsp = false;
		iopads = false;
		fsm_lut4_eval = false;
		fsm_lut4_enabled = false;
		native_carry = true;
		lut_feedback = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		Invocation invocation(*this);
		std::unique_ptr<MuxResourceScope> mux_scope;
		if (!design->scratchpad.count("muxledger.scope"))
			mux_scope.reset(new MuxResourceScope(design));
		if (design->scratchpad_get_bool("opt_fsm_lut4.evaluating")) {
			if (std::find(args.begin(), args.end(), "-fsm-lut4-eval") == args.end())
				log_cmd_error("synth_intel: missing internal FSM evaluation option.\n");
		}
		execute_impl(std::move(args), design);
	}

	void execute_impl(std::vector<std::string> args, RTLIL::Design *design)
	{
		string run_from, run_to;
		bool run_requested = false;
		reset_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-fsm-lut4-eval") {
				if (!design->scratchpad_get_bool("opt_fsm_lut4.evaluating"))
					log_cmd_error("synth_intel: FSM evaluation option is internal.\n");
				fsm_lut4_eval = true;
				continue;
			}
			if (args[argidx] == "-family" && argidx + 1 < args.size()) {
				family_opt = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-vqm" && argidx + 1 < args.size()) {
				vout_file = args[++argidx];
				log_warning("The Quartus backend has not been tested recently and is likely incompatible with modern versions of Quartus.\n");
				continue;
			}
			if (args[argidx] == "-vpr" && argidx + 1 < args.size()) {
				blif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[argidx + 1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos + 1);
				run_requested = true;
				continue;
			}
			if (args[argidx] == "-iopads") {
				iopads = true;
				continue;
			}
			if (args[argidx] == "-dff") {
				dff = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-lut-feedback") {
				lut_feedback = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-retime") {
				// Removed: ABC9 does not support retiming.
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (family_opt == "cyclonev")
			log_cmd_error("Cyclone V synthesis has been moved to synth_intel_alm.\n");

		if (family_opt != "max10" &&
		    family_opt != "cycloneiv" &&
		    family_opt != "cycloneive" &&
		    family_opt != "cyclone10lp")
			log_cmd_error("Invalid or no family specified: '%s'\n", family_opt);

		if (family_opt != "max10")
			nodsp = true;
		if (fsm_lut4_eval) {
			if (family_opt != "cycloneiv" || !design->scratchpad_get_bool("opt_lut4_mapping.evaluating"))
				log_error("synth_intel: invalid joint mapping evaluation context.\n");
			auto mode = design->scratchpad_get_string("opt_lut4_mapping.carry_mode");
			if (mode != "generic" && mode != "native")
				log_error("synth_intel: invalid joint carry evaluation mode.\n");
			native_carry = mode == "native";
		}
		fsm_lut4_enabled = !fsm_lut4_eval && !dff && family_opt == "cycloneiv" && run_from.empty() && run_to.empty();
		if (lut_feedback && (!fsm_lut4_enabled || run_requested))
			log_cmd_error("synth_intel: -lut-feedback requires complete -family cycloneiv synthesis without -dff, -run or an internal evaluation option.\n");
		if (run_from == "fsm_arithmetic" && (!fsm_lut4_eval || dff ||
			!Lut4Mapping::PrefixContext::active() || Lut4Mapping::PrefixContext::active()->design != design))
			log_cmd_error("synth_intel: arithmetic continuation requires an internal combinational coordinator.\n");
		if (Lut4Mapping::FeedbackContinuation::matches(design) &&
			(!fsm_lut4_eval || dff || family_opt != "cycloneiv" || run_from != "map_luts" || run_to != "check" ||
			 design->scratchpad_get_string("opt_lut4_mapping.script_kind") != "feedback-boolean"))
			log_error("synth_intel: invalid typed feedback continuation.\n");
		if (fsm_lut4_eval && design->scratchpad_get_string("opt_lut4_mapping.script_kind") == "feedback-boolean" &&
			!Lut4Mapping::FeedbackContinuation::matches(design))
			log_cmd_error("synth_intel: feedback mapping requires the typed internal continuation.\n");
		if (!fsm_lut4_eval)
			design->scratchpad_unset("opt_fsm_lut4.completed");

		log_header(design, "Executing SYNTH_INTEL pass.\n");
		log_push();

		std::unique_ptr<Lut4Mapping::CommonMuxContext> common_mux;
		if (fsm_lut4_enabled) common_mux = std::make_unique<Lut4Mapping::CommonMuxContext>(design);
		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin")) {
			if (check_label("family"))
				run(stringf("read_verilog -sv -lib +/intel/%s/cells_sim.v", family_opt));

			// Misc and common cells
			run("read_verilog -sv -lib +/intel/common/m9k_bb.v");
			run("read_verilog -sv -lib +/intel/common/altpll_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt));
		}

		if (check_label("coarse")) {
			run("proc");
			if (flatten || help_mode) {
				run("check");
				run("flatten", "(skip if -noflatten)");
			}
			run("tribuf -logic");
			run("deminout");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			if ((family_opt == "cycloneiv" && !fsm_lut4_eval) || help_mode) {
				auto common_started = Lut4Mapping::CommonMuxContext::Clock::now();
				{
					MuxInferSatBudget infer_budget(active_design);
					run("opt_muxinfer", "(if -family cycloneiv)");
				}
				run("opt_expr", "(if -family cycloneiv)");
				run("opt_clean", "(if -family cycloneiv)");
				run("opt_muxcomb", "(if -family cycloneiv)");
				run("opt_muxtree", "(if -family cycloneiv)");
				run("opt_expr", "(if -family cycloneiv)");
				run("opt_clean", "(if -family cycloneiv)");
				if (!help_mode) {
					auto duration = Lut4Mapping::CommonMuxContext::Clock::now() - common_started;
					Lut4Mapping::CommonMuxContext::record(active_design, duration);
					log("synth_intel: common Mux segment actual seconds=%.9f.\n", std::chrono::duration<double>(duration).count());
				}
			}
			if (fsm_lut4_enabled) {
				std::string options = "opt_fsm_lut4 -family " + family_opt;
				if (lut_feedback) options += " -feedback";
				if (nobram) options += " -nobram";
				if (nodsp) options += " -nodsp";
				if (iopads) options += " -iopads";
				if (!flatten) options += " -noflatten";
				run(options);
			}
		}

		bool fsm_mapping_completed = active_design && active_design->scratchpad_get_bool("opt_fsm_lut4.completed");
		bool post_result_reused = false;
		bool prefix_executed = false;
		if (!fsm_mapping_completed && check_label("fsm_entry")) {
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Prefix)) return;
			prefix_executed = true;
			if (!help_mode) Lut4Mapping::PrefixContext::begin(active_design);
			run("fsm");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			if (family_opt == "cycloneiv" || help_mode) {
				run("muxtree_share", "(if -family cycloneiv)");
				run("opt -full -noff", "(if -family cycloneiv)");
				run("opt_muxrebuild -max_vars 10", "(if -family cycloneiv)");
				run("opt_muxcomb", "(if -family cycloneiv)");
				run("opt -full -noff", "(if -family cycloneiv)");
			}
			run("opt_reshape");
			run("opt_expr");
			run("opt_clean");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");

			if (!help_mode) Lut4Mapping::PrefixContext::complete(active_design);
		}

		if (!fsm_mapping_completed && (check_label("fsm_arithmetic") || (prefix_executed && active_run_to == "fsm_entry"))) {
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Arithmetic)) return;
			if (help_mode) {
				run("techmap -map +mul2dsp.v [...]", "(unless -nodsp)");
			} else if (family_opt == "max10" && !nodsp) {
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18  -D DSP_A_MINWIDTH=10 -D DSP_B_MINWIDTH=4 -D DSP_NAME=$__MUL18X18");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18  -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=10 -D DSP_NAME=$__MUL18X18");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=9 -D DSP_B_MAXWIDTH=9  -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=4 -D DSP_NAME=$__MUL9X9");
				run("chtype -set $mul t:$__soft_mul");
				run("alumacc");
				run(stringf("techmap -map +/intel/%s/dsp_map.v", family_opt));
			} else {
				run("alumacc");
			}
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (!fsm_mapping_completed && !nobram && check_label("map_bram", "(skip if -nobram)")) {
			if (family_opt == "cycloneiv" ||
			    family_opt == "cycloneive" ||
			    family_opt == "max10" ||
			    help_mode) {
				run("memory_bram -rules +/intel/common/brams_m9k.txt", "(if applicable for family)");
				run("techmap -map +/intel/common/brams_map_m9k.v", "(if applicable for family)");
			} else {
				log_warning("BRAM mapping is not currently supported for %s.\n", family_opt);
			}
		}

		if (!fsm_mapping_completed && check_label("map_ffram")) {
			run("opt -fast -mux_undef -undriven -fine -full");
			run("memory_map");
			run("opt -undriven -fine");
			if (family_opt == "cycloneiv" && native_carry) {
				run("alumacc");
				run("maccmap");
				run("opt -fast");
				run("opt_cycloneiv_carry");
				run("opt_cycloneiv_carry -clean -check");
			}
			run("techmap -map +/techmap.v");
			run("opt -full");
			run("clean -purge");
			run("setundef -undriven -zero");
			if (family_opt == "cycloneiv")
				run("opt_cycloneiv_carry -clean -check");
		}

		if (!fsm_mapping_completed && check_label("map_ffs")) {
			run("dfflegalize -cell $_DFFE_PN0P_ 01");
			if (help_mode || (family_opt == "cycloneiv" && !dff))
				run("opt_ffphase -prepare");
			run("techmap -map +/intel/common/ff_map.v");
		}

		if (!fsm_mapping_completed && check_label("map_luts")) {
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Abc)) return;
			if (family_opt == "cycloneiv")
				run("opt_cycloneiv_carry -clean -check");
			if (!dff && fsm_lut4_eval) {
				if (!active_design->scratchpad_get_bool("opt_lut4_mapping.evaluating"))
					log_error("synth_intel: missing joint mapping evaluation context.\n");
				run("opt_abc9_area -single-map -script-family " + active_design->scratchpad_get_string("opt_lut4_mapping.script_kind"));
			} else {
				Lut4Mapping::CarryBoundaryGuard carry_boundaries(family_opt == "cycloneiv" ? active_design : nullptr);
				run("abc9 -lut 4 -W 300" + string(dff ? " -dff" : " -script +&put;strash;dch,-f,-W,4,-C,100,-S,1000;if,-K,4,-a,-C,8,-F,1,-A,2,-m,-W,300;lutpack,-N,3,-Q,1,-S,2,-L,0,-s;mfs2,-a,-W,1,-F,8,-D,20,-M,64,-L,0,-C,500;&get,-m"));
			}
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Post)) return;
			run("clean");
			run("opt -fast");
			if (family_opt == "cycloneiv")
				run("opt_cycloneiv_carry -clean -check");
			auto timed_design = !help_mode && fsm_lut4_eval ? active_design : nullptr;
			Lut4Mapping::PostTimer post_timer(timed_design, Lut4Mapping::PostPhase::Complete);
			if (!help_mode && fsm_lut4_eval) {
				if (!Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Lookup)) return;
				Lut4Mapping::PostTimer lookup_timer(timed_design, Lut4Mapping::PostPhase::Lookup);
				post_result_reused = Lut4Mapping::reuse_post_result(active_design);
			}
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Post)) return;
			if (!post_result_reused) {
				{
					if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Resyn)) return;
					Lut4Mapping::PostTimer resyn_timer(timed_design, Lut4Mapping::PostPhase::Resyn);
					if (help_mode || (family_opt == "cycloneiv" && active_design && Lut4Mapping::shared_post(active_design)))
						run("opt_native_ff_lut4");
					run("opt_lutresyn");
				}
				if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Post)) return;
				run("opt_clean");
				{
					if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Resub)) return;
					Lut4Mapping::PostTimer resub_timer(timed_design, Lut4Mapping::PostPhase::Resub);
					run("opt_lutresub");
				}
				if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Post)) return;
				run("opt_clean");
				run("autoname");
				run("clean");
			}
			if (!help_mode && fsm_lut4_eval)
				Lut4Mapping::GenericCheckpointContext::complete(active_design, post_result_reused);
			if (!post_result_reused && family_opt == "cycloneiv" && !dff && (fsm_lut4_eval || (active_run_from.empty() && active_run_to.empty()))) {
				if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Carry)) return;
				Lut4Mapping::PostTimer carry_timer(timed_design, Lut4Mapping::PostPhase::Carry);
				run("opt_cycloneiv_carry -lut");
			}
		}

		if (check_label("map_cells")) {
			if (!fsm_mapping_completed && !post_result_reused) {
				if (iopads || help_mode)
					run("iopadmap -bits -outpad $__outpad I:O -inpad $__inpad O:I", "(if -iopads)");
				run(stringf("techmap -map +/intel/%s/cells_map.v", family_opt));
				run("clean -purge");
			}
			if (family_opt == "cycloneiv")
				run("opt_cycloneiv_carry -clean -check");
			if (help_mode || (family_opt == "cycloneiv" && !dff && !fsm_lut4_eval))
				run("opt_ffphase");
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
			if (!help_mode && !Lut4Mapping::PhaseContext::begin(active_design, Lut4Mapping::MappingPhase::Idle)) return;
		}

		if (check_label("vqm")) {
			if (!vout_file.empty() || help_mode)
				run(stringf("write_verilog -attr2comment -defparam -nohex -decimal -renameprefix syn_ %s",
					    help_mode ? "<file-name>" : vout_file.c_str()));
		}

		if (check_label("vpr")) {
			if (!blif_file.empty() || help_mode) {
				run(stringf("opt_clean -purge"));
				run(stringf("write_blif %s", help_mode ? "<file-name>" : blif_file));
			}
		}
	}
} SynthIntelPass;

PRIVATE_NAMESPACE_END
