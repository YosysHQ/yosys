
all: select.pdf red_or3x1.pdf sym_mul.pdf mymul.pdf mulshift.pdf addshift.pdf \
		macc_simple_xmap.pdf macc_xilinx_xmap.pdf

select.pdf: select.v select.ys
	../../yosys select.ys

red_or3x1.pdf: red_or3x1_*
	../../yosys red_or3x1_test.ys

sym_mul.pdf: sym_mul_*
	../../yosys sym_mul_test.ys

mymul.pdf: mymul_*
	../../yosys mymul_test.ys

mulshift.pdf: mulshift_*
	../../yosys mulshift_test.ys

addshift.pdf: addshift_*
	../../yosys addshift_test.ys

macc_simple_xmap.pdf: macc_simple_*.v macc_simple_test.ys
	../../yosys macc_simple_test.ys

macc_xilinx_xmap.pdf: macc_xilinx_*.v macc_xilinx_test.ys
	../../yosys macc_xilinx_test.ys

