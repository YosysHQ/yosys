
OBJS += passes/opt/opt.o
OBJS += passes/opt/opt_merge.o
OBJS += passes/opt/opt_mem.o
OBJS += passes/opt/opt_mem_feedback.o
OBJS += passes/opt/opt_mem_priority.o
OBJS += passes/opt/opt_mem_widen.o
OBJS += passes/opt/opt_muxtree.o
OBJS += passes/opt/opt_reduce.o
OBJS += passes/opt/opt_dff.o
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
OBJS += passes/opt/opt_ffinv.o
OBJS += passes/opt/pmux2shiftx.o
OBJS += passes/opt/muxpack.o

OBJS += passes/opt/peepopt.o
GENFILES += passes/opt/peepopt_pm.h
passes/opt/peepopt.o: passes/opt/peepopt_pm.h
$(eval $(call add_extra_objs,passes/opt/peepopt_pm.h))

PEEPOPT_PATTERN  = passes/opt/peepopt_shiftmul_right.pmg
PEEPOPT_PATTERN += passes/opt/peepopt_shiftmul_left.pmg
PEEPOPT_PATTERN += passes/opt/peepopt_shiftadd.pmg
PEEPOPT_PATTERN += passes/opt/peepopt_muldiv.pmg
PEEPOPT_PATTERN += passes/opt/peepopt_muldiv_c.pmg
PEEPOPT_PATTERN += passes/opt/peepopt_formal_clockgateff.pmg

passes/opt/peepopt_pm.h: passes/pmgen/pmgen.py $(PEEPOPT_PATTERN)
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $< -o $@ -p peepopt $(filter-out $<,$^)
endif
