OBJS += passes/pmgen/ice40_dsp.o
OBJS += passes/pmgen/peepopt.o

# --------------------------------------

passes/pmgen/ice40_dsp.o: passes/pmgen/ice40_dsp_pm.h
EXTRA_OBJS += passes/pmgen/ice40_dsp_pm.h
.SECONDARY: passes/pmgen/ice40_dsp_pm.h

passes/pmgen/ice40_dsp_pm.h: passes/pmgen/pmgen.py passes/pmgen/ice40_dsp.pmg
	$(P) mkdir -p passes/pmgen && python3 $< -o $@ -p ice40_dsp $(filter-out $<,$^)

# --------------------------------------

passes/pmgen/peepopt.o: passes/pmgen/peepopt_pm.h
EXTRA_OBJS += passes/pmgen/peepopt_pm.h
.SECONDARY: passes/pmgen/peepopt_pm.h

PEEPOPT_PATTERN  = passes/pmgen/peepopt_shiftmul.pmg
PEEPOPT_PATTERN += passes/pmgen/peepopt_muldiv.pmg

passes/pmgen/peepopt_pm.h: passes/pmgen/pmgen.py $(PEEPOPT_PATTERN)
	$(P) mkdir -p passes/pmgen && python3 $< -o $@ -p peepopt $(filter-out $<,$^)
