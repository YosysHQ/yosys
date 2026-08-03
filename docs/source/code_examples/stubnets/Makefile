include ../../../common.mk

.PHONY: all dots examples
all: dots examples
dots:
examples: test

.PHONY: test
test: stubnets.so
	@$(YOSYS) -ql test1.log -m ./stubnets.so test.v -p "stubnets" >/dev/null 2>&1
	@$(YOSYS) -ql test2.log -m ./stubnets.so test.v -p "opt; stubnets" >/dev/null 2>&1
	@$(YOSYS) -ql test3.log -m ./stubnets.so test.v -p "techmap; opt; stubnets -report_bits" >/dev/null 2>&1

stubnets.so: stubnets.cc
	@$(YOSYS_CONFIG) --exec --cxx --cxxflags --ldflags -o $@ -shared $^ --ldlibs >/dev/null 2>&1

.PHONY: clean
clean:
	@rm -f test1.log test2.log test3.log
	@rm -f stubnets.so stubnets.d
