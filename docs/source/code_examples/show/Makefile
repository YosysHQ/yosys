PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

EXAMPLE = example_00 example_01 example_02 example_03
EXAMPLE_DOTS := $(addsuffix .dot,$(EXAMPLE))

CMOS = cmos_00 cmos_01
CMOS_DOTS := $(addsuffix .dot,$(CMOS))

all: splice.dot $(EXAMPLE_DOTS) $(CMOS_DOTS)

splice.dot: splice.v
	$(YOSYS) -p 'proc; opt; show -format dot -prefix splice' splice.v

$(EXAMPLE_DOTS): example.v example.ys
	$(YOSYS) example.ys

cmos_00.dot: cmos.v
	$(YOSYS) -p 'read_verilog cmos.v; techmap; abc -liberty ../intro/mycells.lib;; show -format dot -prefix cmos_00'

cmos_01.dot: cmos.v
	$(YOSYS) -p 'read_verilog cmos.v; techmap; splitnets -ports; abc -liberty ../intro/mycells.lib;; show -lib ../intro/mycells.v -format dot -prefix cmos_01'
