PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOTS = counter_00.dot counter_01.dot counter_02.dot counter_03.dot

all: dots
dots: $(DOTS)

$(DOTS): counter.v counter.ys mycells.lib
	$(YOSYS) counter.ys

.PHONY: clean
clean:
	rm -f *.dot
