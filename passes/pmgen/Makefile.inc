passes/pmgen/%_pm.h: passes/pmgen/pmgen.py passes/pmgen/%.pmg
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $< -o $@ -p $(notdir $*) $(filter-out $<,$^)

# --------------------------------------

OBJS += passes/pmgen/test_pmgen.o
GENFILES += passes/pmgen/test_pmgen_pm.h
passes/pmgen/test_pmgen.o: passes/pmgen/test_pmgen_pm.h techlibs/ice40/ice40_dsp_pm.h techlibs/xilinx/xilinx_srl_pm.h
$(eval $(call add_extra_objs,passes/pmgen/test_pmgen_pm.h))

