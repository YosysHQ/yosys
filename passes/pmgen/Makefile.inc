OBJS += passes/pmgen/ice40_dsp.o

passes/pmgen/ice40_dsp.o: passes/pmgen/ice40_dsp_pm.h
EXTRA_OBJS += passes/pmgen/ice40_dsp_pm.h
.SECONDARY: passes/pmgen/ice40_dsp_pm.h

passes/pmgen/ice40_dsp_pm.h: passes/pmgen/ice40_dsp.pmg passes/pmgen/pmgen.py
	$(P) cd passes/pmgen && python3 pmgen.py ice40_dsp
