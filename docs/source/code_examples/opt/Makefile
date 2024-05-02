PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOT_NAMES = opt_share opt_muxtree opt_merge opt_expr

DOTS := $(addsuffix .dot,$(DOT_NAMES))

all: dots
dots: $(DOTS)

%_full.dot: %.ys
	$(YOSYS) $<

%.dot: %_full.dot
	gvpack -u $*_full.dot -o $@

.PHONY: clean
clean:
	rm -f *.dot
