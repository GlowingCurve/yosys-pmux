// 为 PMUX Pass 共用端口类型查询；内部类型使用静态表，模块类型按实际调用关系登记。
#ifndef PMUX_CELLTYPES_H
#define PMUX_CELLTYPES_H

#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

// 内部类型使用静态端口表，自定义类型仅登记当前模块实际调用的模块。
struct PmuxCellTypes : NewCellTypes {
	PmuxCellTypes(RTLIL::Module *module, RTLIL::Design *design)
	{
		setup();
		for (auto cell : module->cells())
			if (!cell_known(cell->type))
				if (auto definition = design->module(cell->type))
					setup_module(definition);
	}
};

YOSYS_NAMESPACE_END

#endif
