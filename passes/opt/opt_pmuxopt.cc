#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include <cstddef>
#include <stdio.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptPMUXWorker {
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;

	OptPMUXWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module), assign_map(module)
	{
		log("we get something\n");
	}
};

struct OptPmuxPass : public Pass {
	OptPmuxPass() : Pass("opt_pmuxopt", "optimize pmux structure") {}
	void help() override { log("optimize pmux structure; it is under development"); }
	void execute(vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "(under development)optimizing pmux structure\n");
		extra_args(args, 1, design);

		int total_count = 0;
		for (auto module : design->selected_whole_modules_warn()) {
			if (module->has_processes_warn())
				continue;
			OptPMUXWorker worker(design, module);
			total_count += 1;
		}
		if (total_count) {
			design->scratchpad_set_bool("opt.did_something", true);
		}
		log("finished!");
	}
} OptPmuxPass;

PRIVATE_NAMESPACE_END
