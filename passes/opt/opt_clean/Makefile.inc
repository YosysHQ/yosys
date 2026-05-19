OPT_CLEAN_OBJS =
OPT_CLEAN_OBJS += passes/opt/opt_clean/cells_all.o
OPT_CLEAN_OBJS += passes/opt/opt_clean/cells_temp.o
OPT_CLEAN_OBJS += passes/opt/opt_clean/wires.o
OPT_CLEAN_OBJS += passes/opt/opt_clean/inits.o
OPT_CLEAN_OBJS += passes/opt/opt_clean/opt_clean.o

$(OPT_CLEAN_OBJS): passes/opt/opt_clean/opt_clean.h

OBJS += $(OPT_CLEAN_OBJS)
