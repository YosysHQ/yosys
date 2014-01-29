
all: counter_00.pdf counter_01.pdf counter_02.pdf counter_03.pdf

counter_00.pdf: counter.v counter.ys mycells.lib
	../../yosys counter.ys

counter_01.pdf: counter_00.pdf
counter_02.pdf: counter_00.pdf
counter_03.pdf: counter_00.pdf

