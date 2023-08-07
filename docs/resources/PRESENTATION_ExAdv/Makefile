PROGRAM_PREFIX :=

YOSYS ?= ../../../$(PROGRAM_PREFIX)yosys

all: select.pdf red_or3x1.pdf sym_mul.pdf mymul.pdf mulshift.pdf addshift.pdf \
		macc_simple_xmap.pdf macc_xilinx_xmap.pdf

select.pdf: select.v select.ys
	$(YOSYS) select.ys

red_or3x1.pdf: red_or3x1_*
	$(YOSYS) red_or3x1_test.ys

sym_mul.pdf: sym_mul_*
	$(YOSYS) sym_mul_test.ys

mymul.pdf: mymul_*
	$(YOSYS) mymul_test.ys

mulshift.pdf: mulshift_*
	$(YOSYS) mulshift_test.ys

addshift.pdf: addshift_*
	$(YOSYS) addshift_test.ys

macc_simple_xmap.pdf: macc_simple_*.v macc_simple_test.ys
	$(YOSYS) macc_simple_test.ys

macc_xilinx_xmap.pdf: macc_xilinx_*.v macc_xilinx_test.ys
	$(YOSYS) macc_xilinx_test.ys

