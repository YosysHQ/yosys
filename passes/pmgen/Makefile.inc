PMG_SRC = $(wildcard passes/pmgen/*.pmg)
PMG_OBJS += $(patsubst %.pmg, %.o, $(PMG_SRC))
OBJS += $(PMG_OBJS)

$(PMG_OBJS): %.o: %_pm.h

EXTRA_OBJS += $(patsubst %.pmg, %_pm.h, $(PMG_SRC))
.SECONDARY: $(EXTRA_OBJS)

%_pm.h: passes/pmgen/pmgen.py %.pmg
	$(P) mkdir -p passes/pmgen && python3 $^ $@
