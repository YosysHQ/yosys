include ../../../common.mk

.PHONY: all dots examples
all: dots examples
dots: scrambler_p01.dot scrambler_p02.dot
examples:

scrambler_p01.dot scrambler_p02.dot: scrambler.ys scrambler.v
	@$(YOSYS) scrambler.ys >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot
