// 直接生成 Intel LUT、IO buffer 和触发器映射，保留原始单元名称与属性。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "passes/opt/pmux_lut_graph.h"
#include <initializer_list>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void check_cell(Cell *cell, std::initializer_list<IdString> ports)
{
	if (!cell->parameters.empty())
		log_error("Invalid parameter count for %s.%s (%s).\n", log_id(cell->module), log_id(cell), log_id(cell->type));
	if (cell->connections().size() != ports.size())
		log_error("Invalid port count for %s.%s (%s).\n", log_id(cell->module), log_id(cell), log_id(cell->type));
	for (auto port : ports)
		if (!cell->hasPort(port) || GetSize(cell->getPort(port)) != 1)
			log_error("Invalid port %s for %s.%s (%s): expected width 1.\n",
				log_id(port), log_id(cell->module), log_id(cell), log_id(cell->type));
}

void replace_type(Cell *cell, IdString type, const dict<IdString, SigSpec> &connections)
{
	for (auto &connection : connections) cell->unsetPort(connection.first);
	cell->type = type;
}

void map_io(Cell *cell, IdString inputtype, IdString outputtype)
{
	check_cell(cell, {ID::I, ID::O});
	auto connections = cell->connections();
	bool input = cell->type == ID($__inpad);
	replace_type(cell, input ? inputtype : outputtype, connections);
	cell->setPort(ID(i), connections.at(ID::I));
	cell->setPort(ID(o), connections.at(ID::O));
	if (input) cell->setPort(ID(ibar), State::S0);
	else cell->setPort(ID(oe), State::S1);
}

void map_ff(Cell *cell, SigMap &sigmap, FfInitVals &initvals)
{
	check_cell(cell, {ID::D, ID::C, ID::R, ID::E, ID::Q});
	auto connections = cell->connections();
	auto q = sigmap(connections.at(ID::Q));
	bool high = initvals(q[0]) == State::S1;
	// 与 ff_map.v 的 _TECHMAP_REMOVEINIT_Q_ 使用相同的初始化移除接口。
	initvals.remove_init(q);
	replace_type(cell, ID(dffeas), connections);
	cell->setParam(ID(is_wysiwyg), Const("TRUE"));
	cell->setParam(ID(power_up), Const(high ? "high" : "low"));
	cell->setPort(ID(d), connections.at(ID::D));
	cell->setPort(ID(q), connections.at(ID::Q));
	cell->setPort(ID(clk), connections.at(ID::C));
	cell->setPort(ID(clrn), connections.at(ID::R));
	cell->setPort(ID(ena), connections.at(ID::E));
	cell->setPort(ID(prn), State::S1);
	cell->setPort(ID(asdata), State::S0);
	cell->setPort(ID(aload), State::S0);
	cell->setPort(ID(sclr), State::S0);
	cell->setPort(ID(sload), State::S0);
}

struct OptPmuxMapPass : Pass {
	OptPmuxMapPass() : Pass("opt_pmuxmap", "map Intel LUT, IO buffer and flip-flop cells directly") {}
	void help() override
	{
		log("    opt_pmuxmap -family <cycloneiv|cycloneive|cyclone10lp|max10> [selection]\n");
		log("    opt_pmuxmap -ff [selection]\n\n");
		log("Map $lut, $__inpad and $__outpad cells to Intel primitives.\n");
		log("-ff maps $_DFFE_PN0P_ using ff_map.v and consumes its Q initialization.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		std::string family;
		bool ff = false, mode = false;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-ff") {
				if (mode) log_cmd_error("Specify exactly one mapping mode.\n");
				ff = mode = true;
				continue;
			}
			if (args[argidx] == "-family") {
				if (mode) log_cmd_error("Specify exactly one mapping mode.\n");
				if (argidx+1 >= args.size()) log_cmd_error("Missing family for -family.\n");
				family = args[++argidx];
				if (family != "cycloneiv" && family != "cycloneive" && family != "cyclone10lp" && family != "max10")
					log_cmd_error("Unsupported Intel family: %s.\n", family.c_str());
				mode = true;
				continue;
			}
			break;
		}
		if (!mode) log_cmd_error("Specify -family or -ff.\n");
		extra_args(args, argidx, design);
		log_header(design, "Executing OPT_PMUXMAP pass (mapping Intel cells).\n");
		std::string prefix = family == "max10" ? "fiftyfivenm" : family;
		IdString luttype, inputtype, outputtype;
		if (!ff) {
			luttype = RTLIL::escape_id(prefix + "_lcell_comb");
			inputtype = RTLIL::escape_id(prefix + "_io_ibuf");
			outputtype = RTLIL::escape_id(prefix + "_io_obuf");
		}
		for (auto module : design->selected_modules()) {
			SigMap sigmap;
			FfInitVals initvals;
			bool init_ready = false;
			for (auto cell : module->cells()) {
				if (!design->selected(module, cell)) continue;
				if (ff) {
					if (cell->type != ID($_DFFE_PN0P_)) continue;
					if (!init_ready) {
						sigmap.set(module);
						initvals.set(&sigmap, module);
						init_ready = true;
					}
					map_ff(cell, sigmap, initvals);
				} else if (cell->type == ID($lut)) PmuxLutGraph::map_intel_lut(cell, luttype);
				else if (cell->type.in(ID($__inpad), ID($__outpad))) map_io(cell, inputtype, outputtype);
			}
		}
	}
} OptPmuxMapPass;

PRIVATE_NAMESPACE_END
