include ../../../common.mk

.PHONY: all dots examples
all: dots examples
dots: red_or3x1.dot sym_mul.dot mymul.dot mulshift.dot addshift.dot
examples:

red_or3x1.dot: red_or3x1_*
	@$(YOSYS) red_or3x1_test.ys >/dev/null 2>&1

sym_mul.dot: sym_mul_*
	@$(YOSYS) sym_mul_test.ys >/dev/null 2>&1

mymul.dot: mymul_*
	@$(YOSYS) mymul_test.ys >/dev/null 2>&1

mulshift.dot: mulshift_*
	@$(YOSYS) mulshift_test.ys >/dev/null 2>&1

addshift.dot: addshift_*
	@$(YOSYS) addshift_test.ys >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f *.dot
