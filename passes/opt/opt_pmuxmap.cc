// 直接生成 Intel LUT、IO buffer 和触发器映射，保留原始单元名称与属性。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include <initializer_list>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void check_ports(Cell *cell, std::initializer_list<std::pair<IdString, int>> ports)
{
	if (cell->connections().size() != ports.size())
		log_error("Invalid port count for %s.%s (%s).\n", log_id(cell->module), log_id(cell), log_id(cell->type));
	for (auto port : ports)
		if (!cell->hasPort(port.first) || GetSize(cell->getPort(port.first)) != port.second)
			log_error("Invalid port %s for %s.%s (%s): expected width %d.\n",
				log_id(port.first), log_id(cell->module), log_id(cell), log_id(cell->type), port.second);
}

void check_parameters(Cell *cell, std::initializer_list<IdString> parameters)
{
	if (cell->parameters.size() != parameters.size())
		log_error("Invalid parameter count for %s.%s (%s).\n", log_id(cell->module), log_id(cell), log_id(cell->type));
	for (auto parameter : parameters)
		if (!cell->hasParam(parameter))
			log_error("Missing parameter %s for %s.%s (%s).\n",
				log_id(parameter), log_id(cell->module), log_id(cell), log_id(cell->type));
}

void replace_type(Cell *cell, IdString type, const dict<IdString, SigSpec> &connections)
{
	for (auto &connection : connections) cell->unsetPort(connection.first);
	cell->parameters.clear();
	cell->type = type;
}

void map_lut(Cell *cell, IdString luttype)
{
	check_parameters(cell, {ID::WIDTH, ID::LUT});
	const auto &width_parameter = cell->getParam(ID::WIDTH);
	if (!width_parameter.is_fully_def() || !width_parameter.convertible_to_int())
		log_error("Invalid LUT width for %s.%s.\n", log_id(cell->module), log_id(cell));
	int width = width_parameter.as_int();
	if (width < 1 || width > 4)
		log_error("Unsupported LUT width %d for %s.%s.\n", width, log_id(cell->module), log_id(cell));
	check_ports(cell, {{ID::A, width}, {ID::Y, 1}});
	auto connections = cell->connections();
	const auto &a = connections.at(ID::A), &y = connections.at(ID::Y);
	if (width == 1) {
		// cells_map.v 的单输入分支直接执行按位取反。
		replace_type(cell, ID($not), connections);
		cell->setParam(ID::A_SIGNED, false);
		cell->setParam(ID::A_WIDTH, 1);
		cell->setParam(ID::Y_WIDTH, 1);
		cell->setPort(ID::A, a);
		cell->setPort(ID::Y, y);
		return;
	}
	auto lut = cell->getParam(ID::LUT);
	Const mask = lut;
	if (width < 4) {
		mask = Const();
		for (int i = 0; i < (1 << (4-width)); i++) mask.append(lut);
	}
	replace_type(cell, luttype, connections);
	cell->setParam(ID(lut_mask), mask);
	cell->setParam(ID(sum_lutc_input), Const("datac"));
	cell->setPort(ID(dataa), a[0]);
	cell->setPort(ID(datab), a[1]);
	cell->setPort(ID(datac), width >= 3 ? a[2] : SigBit(State::S1));
	cell->setPort(ID(datad), width >= 4 ? a[3] : SigBit(State::S1));
	cell->setPort(ID(combout), y);
}

void map_io(Cell *cell, IdString inputtype, IdString outputtype)
{
	check_parameters(cell, {});
	check_ports(cell, {{ID::I, 1}, {ID::O, 1}});
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
	check_parameters(cell, {});
	check_ports(cell, {{ID::D, 1}, {ID::C, 1}, {ID::R, 1}, {ID::E, 1}, {ID::Q, 1}});
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
		log("Map $lut, $__inpad and $__outpad cells using the Intel cells_map.v rules.\n");
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
				} else if (cell->type == ID($lut)) map_lut(cell, luttype);
				else if (cell->type.in(ID($__inpad), ID($__outpad))) map_io(cell, inputtype, outputtype);
			}
		}
	}
} OptPmuxMapPass;

PRIVATE_NAMESPACE_END
