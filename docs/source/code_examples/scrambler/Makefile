PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

.PHONY: all dots examples
all: dots examples
dots: scrambler_p01.dot scrambler_p02.dot
examples:

scrambler_p01.dot scrambler_p02.dot: scrambler.ys scrambler.v
	$(YOSYS) scrambler.ys

.PHONY: clean
clean:
	rm -f *.dot
