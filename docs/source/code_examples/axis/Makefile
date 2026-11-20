include ../../../common.mk

.PHONY: all dots examples
all: dots examples
dots:
examples: test

.PHONY: test test-buggy test-fixed
test: test-buggy test-fixed

test-buggy:
	@$(YOSYS) -ql axis_test.log axis_test.ys
	@grep -Fq 'SAT proof finished - model found: FAIL!' axis_test.log

test-fixed:
	@$(YOSYS) -ql axis_test_fixed.log axis_test_fixed.ys
	@grep -Fq 'SAT proof finished - no model found: SUCCESS!' axis_test_fixed.log

.PHONY: clean
clean:
	@rm -f axis_test.log axis_test_fixed.log
