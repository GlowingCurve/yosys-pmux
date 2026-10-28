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
// opt 调度组合逻辑与时序优化；复用参数向量，减少循环中的命令拼接与解析。
#include "kernel/register.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptPass : public Pass {
	OptPass() : Pass("opt", "perform simple optimizations") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt [options] [selection]\n");
		log("\n");
		log("This pass calls all the other opt_* passes in a useful order. This performs\n");
		log("a series of trivial optimizations and cleanups. This pass executes the other\n");
		log("passes in the following order:\n");
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
		log("Note: Options in square brackets (such as [-keepdc]) are passed through to\n");
		log("the opt_* commands when given to 'opt'.\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::vector<std::string> opt_clean_args = {"opt_clean"};
		std::vector<std::string> opt_expr_args = {"opt_expr"};
		std::vector<std::string> opt_reduce_args = {"opt_reduce"};
		std::vector<std::string> opt_merge_args = {"opt_merge"};
		std::vector<std::string> opt_dff_args = {"opt_dff"};
		bool opt_share = false;
		bool fast_mode = false;
		bool noff_mode = false;
		bool hier_mode = false;

		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				opt_clean_args.push_back("-purge");
				continue;
			}
			if (args[argidx] == "-mux_undef") {
				opt_expr_args.push_back("-mux_undef");
				continue;
			}
			if (args[argidx] == "-mux_bool") {
				opt_expr_args.push_back("-mux_bool");
				continue;
			}
			if (args[argidx] == "-undriven") {
				opt_expr_args.push_back("-undriven");
				continue;
			}
			if (args[argidx] == "-noclkinv") {
				opt_expr_args.push_back("-noclkinv");
				continue;
			}
			if (args[argidx] == "-fine") {
				opt_expr_args.push_back("-fine");
				opt_reduce_args.push_back("-fine");
				continue;
			}
			if (args[argidx] == "-full") {
				opt_expr_args.push_back("-full");
				opt_reduce_args.push_back("-full");
				opt_share = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				opt_expr_args.push_back("-keepdc");
				opt_dff_args.push_back("-keepdc");
				opt_merge_args.push_back("-keepdc");
				continue;
			}
			if (args[argidx] == "-nodffe") {
				opt_dff_args.push_back("-nodffe");
				continue;
			}
			if (args[argidx] == "-nosdff") {
				opt_dff_args.push_back("-nosdff");
				continue;
			}
			if (args[argidx] == "-sat") {
				opt_dff_args.push_back("-sat");
				continue;
			}
			if (args[argidx] == "-share_all") {
				opt_merge_args.push_back("-share_all");
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
				Pass::call(design, opt_expr_args);
				Pass::call(design, opt_merge_args);
				design->scratchpad_unset("opt.did_something");
				if (!noff_mode)
					Pass::call(design, opt_dff_args);
				if (design->scratchpad_get_bool("opt.did_something") == false)
					break;
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, opt_clean_args);
			}
			Pass::call(design, opt_clean_args);
		}
		else
		{
			Pass::call(design, opt_expr_args);
			auto opt_merge_nomux_args = opt_merge_args;
			opt_merge_nomux_args.insert(opt_merge_nomux_args.begin() + 1, "-nomux");
			Pass::call(design, opt_merge_nomux_args);
			while (1) {
				design->scratchpad_unset("opt.did_something");
				Pass::call(design, "opt_muxtree");
				Pass::call(design, opt_reduce_args);
				Pass::call(design, opt_merge_args);
				if (opt_share)
					Pass::call(design, "opt_share");
				if (!noff_mode)
					Pass::call(design, opt_dff_args);
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, opt_clean_args);
				Pass::call(design, opt_expr_args);
				if (design->scratchpad_get_bool("opt.did_something") == false)
					break;
			}
		}

		design->optimize();
		design->check();

		log_pop();
	}
} OptPass;

PRIVATE_NAMESPACE_END
