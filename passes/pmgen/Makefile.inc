%_pm.h: passes/pmgen/pmgen.py %.pmg
	$(P) mkdir -p passes/pmgen && $(PYTHON_EXECUTABLE) $< -o $@ -p $(subst _pm.h,,$(notdir $@)) $(filter-out $<,$^)

# --------------------------------------

OBJS += passes/pmgen/test_pmgen.o
passes/pmgen/test_pmgen.o: passes/pmgen/test_pmgen_pm.h passes/pmgen/ice40_dsp_pm.h passes/pmgen/peepopt_pm.h passes/pmgen/xilinx_srl_pm.h
$(eval $(call add_extra_objs,passes/pmgen/test_pmgen_pm.h))

# --------------------------------------

OBJS += passes/pmgen/ice40_dsp.o
passes/pmgen/ice40_dsp.o: passes/pmgen/ice40_dsp_pm.h
$(eval $(call add_extra_objs,passes/pmgen/ice40_dsp_pm.h))

# --------------------------------------

OBJS += passes/pmgen/ice40_wrapcarry.o
passes/pmgen/ice40_wrapcarry.o: passes/pmgen/ice40_wrapcarry_pm.h
$(eval $(call add_extra_objs,passes/pmgen/ice40_wrapcarry_pm.h))

# --------------------------------------

OBJS += passes/pmgen/xilinx_dsp.o
passes/pmgen/xilinx_dsp.o: passes/pmgen/xilinx_dsp_pm.h passes/pmgen/xilinx_dsp48a_pm.h passes/pmgen/xilinx_dsp_CREG_pm.h passes/pmgen/xilinx_dsp_cascade_pm.h
$(eval $(call add_extra_objs,passes/pmgen/xilinx_dsp_pm.h))
$(eval $(call add_extra_objs,passes/pmgen/xilinx_dsp48a_pm.h))
$(eval $(call add_extra_objs,passes/pmgen/xilinx_dsp_CREG_pm.h))
$(eval $(call add_extra_objs,passes/pmgen/xilinx_dsp_cascade_pm.h))

# --------------------------------------

OBJS += passes/pmgen/peepopt.o
passes/pmgen/peepopt.o: passes/pmgen/peepopt_pm.h
$(eval $(call add_extra_objs,passes/pmgen/peepopt_pm.h))

PEEPOPT_PATTERN  = passes/pmgen/peepopt_shiftmul.pmg
PEEPOPT_PATTERN += passes/pmgen/peepopt_muldiv.pmg
PEEPOPT_PATTERN += passes/pmgen/peepopt_dffmux.pmg

passes/pmgen/peepopt_pm.h: passes/pmgen/pmgen.py $(PEEPOPT_PATTERN)
	$(P) mkdir -p passes/pmgen && $(PYTHON_EXECUTABLE) $< -o $@ -p peepopt $(filter-out $<,$^)

# --------------------------------------

OBJS += passes/pmgen/xilinx_srl.o
passes/pmgen/xilinx_srl.o: passes/pmgen/xilinx_srl_pm.h
$(eval $(call add_extra_objs,passes/pmgen/xilinx_srl_pm.h))
