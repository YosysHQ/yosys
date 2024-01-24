PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

.PHONY: all dots
all: dots
dots: red_or3x1.dot sym_mul.dot mymul.dot mulshift.dot addshift.dot

red_or3x1.dot: red_or3x1_*
	$(YOSYS) red_or3x1_test.ys

sym_mul.dot: sym_mul_*
	$(YOSYS) sym_mul_test.ys

mymul.dot: mymul_*
	$(YOSYS) mymul_test.ys

mulshift.dot: mulshift_*
	$(YOSYS) mulshift_test.ys

addshift.dot: addshift_*
	$(YOSYS) addshift_test.ys

.PHONY: clean
clean:
	rm -f *.dot
