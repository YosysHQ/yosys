
all: select_01.pdf red_or3x1.pdf sym_mul.pdf mymul.pdf mulshift.pdf addshift.pdf

select_01.pdf: select_01.v select_01.ys
	../../yosys select_01.ys

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

