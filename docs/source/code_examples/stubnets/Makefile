PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

.PHONY: all dots examples
all: dots examples
dots:
examples:

.PHONY: test
test: stubnets.so
	$(YOSYS) -ql test1.log -m ./stubnets.so test.v -p "stubnets"
	$(YOSYS) -ql test2.log -m ./stubnets.so test.v -p "opt; stubnets"
	$(YOSYS) -ql test3.log -m ./stubnets.so test.v -p "techmap; opt; stubnets -report_bits"
	tail test1.log test2.log test3.log

stubnets.so: stubnets.cc
	$(YOSYS)-config --exec --cxx --cxxflags --ldflags -o $@ -shared $^ --ldlibs

.PHONY: clean
clean:
	rm -f test1.log test2.log test3.log
	rm -f stubnets.so stubnets.d
