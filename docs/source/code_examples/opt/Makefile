include ../../../common.mk

DOT_NAMES = opt_share opt_muxtree opt_merge opt_expr

DOTS := $(addsuffix .dot,$(DOT_NAMES))

.PHONY: all dots examples
all: dots examples
dots: $(DOTS)
examples:

%.dot: %.ys
	@$(YOSYS) $< >/dev/null 2>&1
	@gvpack -u -o $@ $*_full.dot >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot
