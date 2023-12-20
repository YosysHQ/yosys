PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOT_NAMES = addr_gen_hier addr_gen_proc addr_gen_clean
DOT_NAMES += rdata_proc rdata_flat rdata_adffe rdata_memrdv2 rdata_alumacc
DOT_NAMES += rdata_coarse rdata_map_ram rdata_map_ffram rdata_map_gates 
DOT_NAMES += rdata_map_ffs rdata_map_luts rdata_map_cells

DOTS := $(addsuffix .dot,$(DOT_NAMES))

dots: $(DOTS) fifo.out

$(DOTS) fifo.out: fifo.v fifo.ys
	$(YOSYS) fifo.ys -l fifo.out -Q -T

.PHONY: clean
clean:
	rm -f *.dot
