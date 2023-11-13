PROGRAM_PREFIX :=

YOSYS ?= ../../../$(PROGRAM_PREFIX)yosys

all: macc_simple_xmap.pdf macc_xilinx_xmap.pdf

macc_simple_xmap.pdf: macc_simple_*.v macc_simple_test.ys
	$(YOSYS) macc_simple_test.ys

macc_xilinx_xmap.pdf: macc_xilinx_*.v macc_xilinx_test.ys
	$(YOSYS) macc_xilinx_test.ys

