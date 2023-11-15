PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

EXAMPLE = example_00 example_01 example_02
EXAMPLE_DOTS := $(addsuffix .dot,$(EXAMPLE))

CMOS = cmos_00 cmos_01
CMOS_DOTS := $(addsuffix .dot,$(CMOS))

dots: splice.dot $(EXAMPLE_DOTS) $(CMOS_DOTS)

splice.dot: splice.v
	$(YOSYS) -p 'prep -top splice_demo; show -format dot -prefix splice' splice.v

$(EXAMPLE_DOTS): example.v example.ys
	$(YOSYS) example.ys

$(CMOS_DOTS): cmos.v cmos.ys
	$(YOSYS) cmos.ys

.PHONY: clean
clean:
	rm -rf *.dot
