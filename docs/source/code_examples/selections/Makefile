PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

SUMPROD = sumprod_00 sumprod_01 sumprod_02 sumprod_03 sumprod_04 sumprod_05
SUMPROD_DOTS := $(addsuffix .dot,$(SUMPROD))

MEMDEMO = memdemo_00 memdemo_01
MEMDEMO_DOTS := $(addsuffix .dot,$(MEMDEMO))

SUBMOD = submod_00 submod_01 submod_02 submod_03
SUBMOD_DOTS := $(addsuffix .dot,$(SUBMOD))

all: select.dot $(SUMPROD_DOTS) $(MEMDEMO_DOTS)

select.dot: select.v select.ys
	$(YOSYS) select.ys

$(SUMPROD_DOTS): sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select a:sumstuff; show -format dot -prefix sumprod_00' sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select a:sumstuff %x; show -format dot -prefix sumprod_01' sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select prod; show -format dot -prefix sumprod_02' sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select prod %ci; show -format dot -prefix sumprod_03' sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select prod %ci2; show -format dot -prefix sumprod_04' sumprod.v
	$(YOSYS) -p 'opt; cd sumprod; select prod %ci3; show -format dot -prefix sumprod_05' sumprod.v

$(MEMDEMO_DOTS): memdemo.v
	$(YOSYS) -p 'proc; opt; memory; opt; cd memdemo; show -format dot -prefix memdemo_00' memdemo.v
	$(YOSYS) -p 'proc; opt; memory; opt; cd memdemo; show -format dot -prefix memdemo_01 y %ci2:+$dff[Q,D] %ci*:-$mux[S]:-$dff' memdemo.v

$(SUBMOD_DOTS): submod.ys memdemo.v
	$(YOSYS) submod.ys
