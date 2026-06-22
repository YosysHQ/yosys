include ../../../common.mk

EXAMPLE = example_first example_second example_third
EXAMPLE_DOTS := $(addsuffix .dot,$(EXAMPLE))

CMOS = cmos_00 cmos_01
CMOS_DOTS := $(addsuffix .dot,$(CMOS))

.PHONY: all dots examples
all: dots examples
dots: splice.dot $(EXAMPLE_DOTS) $(CMOS_DOTS)
examples: example.out

splice.dot: splice.v
	@$(YOSYS) -p 'prep -top splice_demo; show -format dot -prefix splice' splice.v >/dev/null 2>&1

$(EXAMPLE_DOTS): example.v example.ys
	@$(YOSYS) example.ys >/dev/null 2>&1

example.out: example_lscd.ys example.v
	@$(YOSYS) $< -l $@ -Q -T >/dev/null 2>&1

$(CMOS_DOTS): cmos.v cmos.ys
	@$(YOSYS) cmos.ys >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -rf *.dot
	@rm -f example.out
