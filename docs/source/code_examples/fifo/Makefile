PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOTS = addr_gen_hier.dot addr_gen_proc.dot
DOTS += rdata_proc.dot rdata_flat.dot
DOTS += fifo_flat.dot fifo_synth.dot

dots: $(DOTS) fifo.out

$(DOTS) fifo.out: fifo.v fifo.ys
	$(YOSYS) fifo.ys -l fifo.out -Q

.PHONY: clean
clean:
	rm -f *.dot
