#ifndef OPT_LUT_FF_BOUNDARY_H
#define OPT_LUT_FF_BOUNDARY_H

#include "kernel/yosys.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN
namespace LutFfBoundary {

// 核实 Intel cells_sim 的库声明，全部端口均为单个 bit。
template<typename CellTypeTable>
inline bool native_dffeas_declared(Design *design, const CellTypeTable &types)
{
	auto declaration = design->module(ID(dffeas));
	if (!declaration || !declaration->get_bool_attribute(ID::blackbox) ||
	    !types.cell_known(ID(dffeas)) || GetSize(declaration->ports) != 10) return false;
	if (GetSize(declaration->parameter_default_values) != 2 ||
	    !declaration->parameter_default_values.count(ID(power_up)) ||
	    !declaration->parameter_default_values.count(ID(is_wysiwyg)) ||
	    declaration->parameter_default_values.at(ID(power_up)) != Const("dontcare") ||
	    declaration->parameter_default_values.at(ID(is_wysiwyg)) != Const("false")) return false;
	for (auto port : {ID(d), ID(clk), ID(clrn), ID(prn), ID(ena), ID(asdata), ID(aload), ID(sclr), ID(sload), ID(q)}) {
		auto wire = declaration->wire(port);
		bool output = port == ID(q);
		if (!wire || wire->width != 1 || wire->port_input == output || wire->port_output != output ||
		    types.cell_input(ID(dffeas), port) == output || types.cell_output(ID(dffeas), port) != output) return false;
	}
	return true;
}

// 仅接受完整的原生 FF 接口，组合图继续保留其他模块的真实依赖。
inline bool sequential(Cell *cell, bool native_dffeas)
{
	if (StaticCellTypes::categories.is_ff(cell->type)) return true;
	if (!native_dffeas || cell->type != ID(dffeas) || GetSize(cell->connections()) != 10) return false;
	for (auto port : {ID(d), ID(clk), ID(clrn), ID(prn), ID(ena), ID(asdata), ID(aload), ID(sclr), ID(sload), ID(q)})
		if (!cell->hasPort(port) || GetSize(cell->getPort(port)) != 1) return false;
	for (auto &parameter : cell->parameters)
		if (!parameter.first.in(ID(power_up), ID(is_wysiwyg))) return false;
	return true;
}

}
YOSYS_NAMESPACE_END

#endif
