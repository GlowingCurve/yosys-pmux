/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/register.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"
#include <initializer_list>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool has_cells(RTLIL::Design *design, std::initializer_list<RTLIL::IdString> types)
{
	for (auto module : design->selected_modules())
		for (auto cell : module->cells()) {
			if (!design->selected(module, cell)) continue;
			for (auto type : types)
				if (cell->type == type)
					return true;
		}
	return false;
}

bool has_share_cells(RTLIL::Design *design)
{
	for (auto module : design->selected_modules()) {
		bool has_mux = false;
		int operators = 0;
		for (auto cell : module->cells()) {
			if (!design->selected(module, cell)) continue;
			has_mux |= cell->type.in(ID($mux), ID($pmux), ID($_MUX_));
			if (operators < 2 && cell->type.in(
					ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_),
					ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_),
					ID($and), ID($or), ID($xor), ID($xnor),
					ID($logic_and), ID($logic_or),
					ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
					ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
					ID($add), ID($sub), ID($mul), ID($div), ID($mod),
					ID($divfloor), ID($modfloor), ID($concat), ID($alu)))
				operators++;
			if (has_mux && operators == 2)
				return true;
		}
	}
	return false;
}

bool has_dff_cells_or_init(RTLIL::Design *design)
{
	for (auto module : design->selected_modules()) {
		for (auto cell : module->cells())
			if (design->selected(module, cell) && cell->is_builtin_ff())
				return true;
		// opt_dff 会检查模块内全部 init 属性的冲突。
		for (auto wire : module->wires())
			if (wire->attributes.count(ID::init))
				return true;
	}
	return false;
}

struct OptPmuxPrepPass : public Pass {
	OptPmuxPrepPass() : Pass("opt_pmuxprep", "perform candidate-aware simple optimizations for Intel synthesis") { }

	void help() override
	{
		log("\n");
		log("    opt_pmuxprep [options] [selection]\n");
		log("\n");
		log("This pass uses the opt pass ordering and options. Calls to opt_muxtree,\n");
		log("opt_reduce, opt_share and opt_dff are skipped when the selected design\n");
		log("does not contain their required cell types. opt_dff is also retained for\n");
		log("init attributes and option validation.\n");
		log("\n");
		log("    opt_expr [-mux_undef] [-mux_bool] [-undriven] [-noclkinv] [-fine] [-full] [-keepdc]\n");
		log("    opt_merge [-share_all] -nomux\n");
		log("\n");
		log("    do\n");
		log("        opt_muxtree\n");
		log("        opt_reduce [-fine] [-full]\n");
		log("        opt_merge [-share_all]\n");
		log("        opt_share  (-full only)\n");
		log("        opt_dff [-nodffe] [-nosdff] [-keepdc] [-sat]  (except when called with -noff)\n");
		log("        opt_hier (-hier only)\n");
		log("        opt_clean [-purge]\n");
		log("        opt_expr [-mux_undef] [-mux_bool] [-undriven] [-noclkinv] [-fine] [-full] [-keepdc]\n");
		log("    while <changed design>\n");
		log("\n");
		log("When called with -fast the following script is used instead:\n");
		log("\n");
		log("    do\n");
		log("        opt_expr [-mux_undef] [-mux_bool] [-undriven] [-noclkinv] [-fine] [-full] [-keepdc]\n");
		log("        opt_merge [-share_all]\n");
		log("        opt_dff [-nodffe] [-nosdff] [-keepdc] [-sat]  (except when called with -noff)\n");
		log("        opt_hier (-hier only)\n");
		log("        opt_clean [-purge]\n");
		log("    while <changed design in opt_dff>\n");
		log("\n");
		log("Options in square brackets are passed through to the corresponding commands.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string opt_clean_args;
		std::string opt_expr_args;
		std::string opt_reduce_args;
		std::string opt_merge_args;
		std::string opt_dff_args;
		bool opt_share = false;
		bool fast_mode = false;
		bool noff_mode = false;
		bool hier_mode = false;
		bool keepdc_mode = false;
		bool sat_mode = false;

		log_header(design, "Executing OPT_PMUXPREP pass (performing simple optimizations).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				opt_clean_args += " -purge";
				continue;
			}
			if (args[argidx] == "-mux_undef") {
				opt_expr_args += " -mux_undef";
				continue;
			}
			if (args[argidx] == "-mux_bool") {
				opt_expr_args += " -mux_bool";
				continue;
			}
			if (args[argidx] == "-undriven") {
				opt_expr_args += " -undriven";
				continue;
			}
			if (args[argidx] == "-noclkinv") {
				opt_expr_args += " -noclkinv";
				continue;
			}
			if (args[argidx] == "-fine") {
				opt_expr_args += " -fine";
				opt_reduce_args += " -fine";
				continue;
			}
			if (args[argidx] == "-full") {
				opt_expr_args += " -full";
				opt_reduce_args += " -full";
				opt_share = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				opt_expr_args += " -keepdc";
				opt_dff_args += " -keepdc";
				opt_merge_args += " -keepdc";
				keepdc_mode = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				opt_dff_args += " -nodffe";
				continue;
			}
			if (args[argidx] == "-nosdff") {
				opt_dff_args += " -nosdff";
				continue;
			}
			if (args[argidx] == "-sat") {
				opt_dff_args += " -sat";
				sat_mode = true;
				continue;
			}
			if (args[argidx] == "-share_all") {
				opt_merge_args += " -share_all";
				continue;
			}
			if (args[argidx] == "-fast") {
				fast_mode = true;
				continue;
			}
			if (args[argidx] == "-noff") {
				noff_mode = true;
				continue;
			}
			if (args[argidx] == "-hier") {
				hier_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (fast_mode)
		{
			while (1) {
				Pass::call(design, "opt_expr" + opt_expr_args);
				Pass::call(design, "opt_merge" + opt_merge_args);
				design->scratchpad_unset("opt.did_something");
				if (!noff_mode && ((sat_mode && keepdc_mode) || has_dff_cells_or_init(design)))
					Pass::call(design, "opt_dff" + opt_dff_args);
				if (design->scratchpad_get_bool("opt.did_something") == false)
					break;
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, "opt_clean" + opt_clean_args);
				log_header(design, "Rerunning OPT_PMUXPREP passes. (Removed registers in this run.)\n");
			}
			Pass::call(design, "opt_clean" + opt_clean_args);
		}
		else
		{
			Pass::call(design, "opt_expr" + opt_expr_args);
			Pass::call(design, "opt_merge -nomux" + opt_merge_args);
			while (1) {
				design->scratchpad_unset("opt.did_something");
				// 每次调用之前读取当前类型，前面的 Pass 可以重新生成候选 cell。
				if (has_cells(design, {ID($mux), ID($pmux)}))
					Pass::call(design, "opt_muxtree");
				if (has_cells(design, {ID($reduce_and), ID($reduce_or), ID($mux), ID($pmux), ID($bmux), ID($demux)}))
					Pass::call(design, "opt_reduce" + opt_reduce_args);
				Pass::call(design, "opt_merge" + opt_merge_args);
				if (opt_share && has_share_cells(design))
					Pass::call(design, "opt_share");
				if (!noff_mode && ((sat_mode && keepdc_mode) || has_dff_cells_or_init(design)))
					Pass::call(design, "opt_dff" + opt_dff_args);
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, "opt_clean" + opt_clean_args);
				Pass::call(design, "opt_expr" + opt_expr_args);
				if (design->scratchpad_get_bool("opt.did_something") == false)
					break;
				log_header(design, "Rerunning OPT_PMUXPREP passes. (Maybe there is more to do..)\n");
			}
		}

		design->optimize();
		design->check();

		log_header(design, "Finished OPT_PMUXPREP passes.%s\n", fast_mode ? "" : " (There is nothing left to do.)");
		log_pop();
	}
} OptPmuxPrepPass;

PRIVATE_NAMESPACE_END
