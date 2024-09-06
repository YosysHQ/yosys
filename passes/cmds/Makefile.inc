
ifeq ($(DISABLE_SPAWN),0)
OBJS += passes/cmds/exec.o
endif
OBJS += passes/cmds/add.o
OBJS += passes/cmds/delete.o
OBJS += passes/cmds/design.o
OBJS += passes/cmds/select.o
OBJS += passes/cmds/show.o
OBJS += passes/cmds/viz.o
OBJS += passes/cmds/rename.o
OBJS += passes/cmds/autoname.o
OBJS += passes/cmds/connect.o
OBJS += passes/cmds/scatter.o
OBJS += passes/cmds/setundef.o
OBJS += passes/cmds/splitnets.o
OBJS += passes/cmds/splitcells.o
OBJS += passes/cmds/stat.o
OBJS += passes/cmds/internal_stats.o
OBJS += passes/cmds/setattr.o
OBJS += passes/cmds/copy.o
OBJS += passes/cmds/splice.o
OBJS += passes/cmds/scc.o
OBJS += passes/cmds/glift.o
OBJS += passes/cmds/torder.o
OBJS += passes/cmds/logcmd.o
OBJS += passes/cmds/tee.o
OBJS += passes/cmds/write_file.o
OBJS += passes/cmds/connwrappers.o
OBJS += passes/cmds/cover.o
OBJS += passes/cmds/trace.o
OBJS += passes/cmds/plugin.o
OBJS += passes/cmds/check.o
OBJS += passes/cmds/qwp.o
OBJS += passes/cmds/edgetypes.o
OBJS += passes/cmds/portlist.o
OBJS += passes/cmds/chformal.o
OBJS += passes/cmds/chtype.o
OBJS += passes/cmds/blackbox.o
OBJS += passes/cmds/ltp.o
ifeq ($(DISABLE_SPAWN),0)
OBJS += passes/cmds/bugpoint.o
endif
OBJS += passes/cmds/scratchpad.o
OBJS += passes/cmds/logger.o
OBJS += passes/cmds/printattrs.o
OBJS += passes/cmds/sta.o
OBJS += passes/cmds/clean_zerowidth.o
OBJS += passes/cmds/xprop.o
OBJS += passes/cmds/dft_tag.o
OBJS += passes/cmds/future.o
OBJS += passes/cmds/box_derive.o
OBJS += passes/cmds/example_dt.o
