
TARGETS += proc_01 proc_02 proc_03
TARGETS += memory_01 memory_02
TARGETS += techmap_01

PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOTS = $(addsuffix .dot,$(TARGETS))

dots: $(DOTS)

%.dot: %.v %.ys
	$(YOSYS) -p 'script $*.ys; show -notitle -prefix $* -format dot'

.PHONY: clean
clean:
	rm -f *.dot

