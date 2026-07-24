include ../../../common.mk

DOTS = counter_00.dot counter_01.dot counter_02.dot counter_03.dot

.PHONY: all dots examples
all: dots examples
dots: $(DOTS)
examples:

$(DOTS): counter.v counter.ys mycells.lib
	@$(YOSYS) counter.ys >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot
	@rm -f synth.v
