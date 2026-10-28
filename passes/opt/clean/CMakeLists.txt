# 将单元、信号和初始化清理编译为 opt_clean，同时注册 clean 命令。
yosys_pass(opt_clean
	cells_all.cc
	cells_temp.cc
	wires.cc
	inits.cc
	opt_clean.cc
	opt_clean.h
	keep_cache.h
	PROVIDES
		clean
)
