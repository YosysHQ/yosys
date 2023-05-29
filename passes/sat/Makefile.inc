
OBJS += passes/sat/sat.o
OBJS += passes/sat/freduce.o
OBJS += passes/sat/eval.o
ifeq ($(ENABLE_ZLIB),1)
OBJS += passes/sat/sim.o
endif
OBJS += passes/sat/miter.o
OBJS += passes/sat/expose.o
OBJS += passes/sat/assertpmux.o
OBJS += passes/sat/clk2fflogic.o
OBJS += passes/sat/async2sync.o
OBJS += passes/sat/formalff.o
OBJS += passes/sat/supercover.o
OBJS += passes/sat/fmcombine.o
OBJS += passes/sat/mutate.o
OBJS += passes/sat/cutpoint.o
OBJS += passes/sat/fminit.o
OBJS += passes/sat/recover_names.o
ifeq ($(DISABLE_SPAWN),0)
OBJS += passes/sat/qbfsat.o
endif
OBJS += passes/sat/synthprop.o
