PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOT_NAMES = opt_share opt_muxtree opt_merge opt_expr

DOTS := $(addsuffix .dot,$(DOT_NAMES))

.PHONY: all dots examples
all: dots examples
dots: $(DOTS)
examples:

%.dot: %.ys
	$(YOSYS) $<
	gvpack -u -o $@ $*_full.dot

.PHONY: clean
clean:
	rm -f *.dot
