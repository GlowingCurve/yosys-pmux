# 将反馈、常量和等价位分析编译为 opt_dff，并声明 simplemap 依赖。
yosys_pass(opt_dff
	opt_dff.cc
	simple.cc
	constbits.cc
	eqbits.cc
	opt_dff.h
	REQUIRES
		simplemap
)
