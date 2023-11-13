PROGRAM_PREFIX :=

YOSYS ?= ../../../$(PROGRAM_PREFIX)yosys

all: counter_00.dot counter_01.dot counter_02.dot counter_03.dot

counter_00.dot: counter.v counter.ys mycells.lib
	$(YOSYS) counter_outputs.ys

counter_01.dot: counter_00.dot
counter_02.dot: counter_00.dot
counter_03.dot: counter_00.dot

