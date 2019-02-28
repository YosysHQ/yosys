OBJS += passes/pmgen/ice40_dsp.o

passes/pmgen/ice40_dsp.o: passes/pmgen/ice40_dsp_pm.h
EXTRA_OBJS += passes/pmgen/ice40_dsp_pm.h
.SECONDARY: passes/pmgen/ice40_dsp_pm.h

passes/pmgen/ice40_dsp_pm.h: passes/pmgen/pmgen.py passes/pmgen/ice40_dsp.pmg
	$(P) mkdir -p passes/pmgen && python3 $^
