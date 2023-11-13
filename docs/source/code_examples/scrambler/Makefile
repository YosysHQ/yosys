PROGRAM_PREFIX :=

YOSYS ?= ../../../$(PROGRAM_PREFIX)yosys

all: scrambler_p01.dot scrambler_p02.dot

scrambler_p01.dot scrambler_p02.dot: scrambler.ys scrambler.v
	$(YOSYS) scrambler.ys
