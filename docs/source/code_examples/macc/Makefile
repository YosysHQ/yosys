include ../../../common.mk

DOTS = macc_simple_xmap.dot macc_xilinx_xmap.dot

.PHONY: all dots examples
all: dots examples
dots: $(DOTS)
examples:

macc_simple_xmap.dot: macc_simple_*.v macc_simple_test.ys
	@$(YOSYS) macc_simple_test.ys >/dev/null 2>&1

macc_xilinx_xmap.dot: macc_xilinx_*.v macc_xilinx_test.ys
	@$(YOSYS) macc_xilinx_test.ys >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot

