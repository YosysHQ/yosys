include ../../../common.mk

DOT_TARGETS += proc_01 proc_02 proc_03
DOT_TARGETS += memory_01 memory_02
DOT_TARGETS += techmap_01

DOTS = $(addsuffix .dot,$(DOT_TARGETS))

.PHONY: all dots examples
all: dots examples
dots: $(DOTS)
examples:

%.dot: %.v %.ys
	@$(YOSYS) -p 'script $*.ys; show -notitle -prefix $* -format dot' >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot
