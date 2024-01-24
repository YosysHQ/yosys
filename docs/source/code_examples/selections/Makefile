PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

SUMPROD = sumprod_00 sumprod_01 sumprod_02 sumprod_03 sumprod_04 sumprod_05
SUMPROD_DOTS := $(addsuffix .dot,$(SUMPROD))

MEMDEMO = memdemo_00 memdemo_01
MEMDEMO_DOTS := $(addsuffix .dot,$(MEMDEMO))

SUBMOD = submod_00 submod_01 submod_02 submod_03
SUBMOD_DOTS := $(addsuffix .dot,$(SUBMOD))

.PHONY: all dots
all: dots
dots: select.dot $(SUMPROD_DOTS) $(MEMDEMO_DOTS) $(SUBMOD_DOTS)

select.dot: select.v select.ys
	$(YOSYS) select.ys

$(SUMPROD_DOTS): sumprod.v sumprod.ys
	$(YOSYS) sumprod.ys

$(MEMDEMO_DOTS): memdemo.v memdemo.ys
	$(YOSYS) memdemo.ys

$(SUBMOD_DOTS): memdemo.v submod.ys
	$(YOSYS) submod.ys

.PHONY: clean
clean:
	rm -rf *.dot
