
OBJS += passes/opt/opt.o
OBJS += passes/opt/opt_merge.o
OBJS += passes/opt/opt_muxtree.o
OBJS += passes/opt/opt_reduce.o
OBJS += passes/opt/opt_rmdff.o
OBJS += passes/opt/opt_clean.o
OBJS += passes/opt/opt_expr.o

ifneq ($(SMALL),1)
OBJS += passes/opt/share.o
OBJS += passes/opt/wreduce.o
endif

