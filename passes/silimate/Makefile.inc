
OBJS += passes/silimate/activity.o
OBJS += passes/silimate/annotate_cell_fanout.o
OBJS += passes/silimate/breakreduce.o
OBJS += passes/silimate/breaksop.o
OBJS += passes/silimate/bus_rebuild.o
OBJS += passes/silimate/fanoutbuf.o
OBJS += passes/silimate/lut2bmux.o
OBJS += passes/silimate/obs_clean.o
OBJS += passes/silimate/opt_balance_tree.o
OBJS += passes/silimate/segv.o
OBJS += passes/silimate/splitfanout.o
OBJS += passes/silimate/splitlarge.o
OBJS += passes/silimate/splitnetlist.o

OBJS += passes/silimate/opt_expand.o
GENFILES += passes/silimate/peepopt_expand.h
passes/silimate/opt_expand.o: passes/silimate/peepopt_expand.h
$(eval $(call add_extra_objs,passes/silimate/peepopt_expand.h))

PEEPOPT_PATTERN  = passes/silimate/peepopt_expand.pmg

passes/silimate/peepopt_expand.h: passes/pmgen/pmgen.py $(PEEPOPT_PATTERN)
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $< -o $@ -p peepopt $(filter-out $<,$^)

OBJS += passes/silimate/muxmode.o
GENFILES += passes/silimate/peepopt_muxmode.h
passes/silimate/muxmode.o: passes/silimate/peepopt_muxmode.h
$(eval $(call add_extra_objs,passes/silimate/peepopt_muxmode.h))

PEEPOPT_PATTERN  = passes/silimate/peepopt_muxmode.pmg
PEEPOPT_PATTERN += passes/silimate/peepopt_muxinvprop.pmg

passes/silimate/peepopt_muxmode.h: passes/pmgen/pmgen.py $(PEEPOPT_PATTERN)
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $< -o $@ -p peepopt $(filter-out $<,$^)
