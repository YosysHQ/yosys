
OBJS += passes/opt/opt.o
OBJS += passes/opt/opt_merge.o
OBJS += passes/opt/opt_mem.o
OBJS += passes/opt/opt_muxtree.o
OBJS += passes/opt/opt_reduce.o
OBJS += passes/opt/opt_rmdff.o
OBJS += passes/opt/opt_share.o
OBJS += passes/opt/opt_clean.o
OBJS += passes/opt/opt_expr.o

ifneq ($(SMALL),1)
OBJS += passes/opt/share.o
OBJS += passes/opt/wreduce.o
OBJS += passes/opt/opt_demorgan.o
OBJS += passes/opt/rmports.o
OBJS += passes/opt/opt_lut.o
OBJS += passes/opt/opt_lut_ins.o
OBJS += passes/opt/pmux2shiftx.o
OBJS += passes/opt/muxpack.o
endif
