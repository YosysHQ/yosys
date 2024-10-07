PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

.PHONY: all dots examples
all: dots examples
dots: test1.dot
examples: test0.log test1.log test2.log

CXXFLAGS=$(shell $(YOSYS)-config --cxxflags)
DATDIR=$(shell $(YOSYS)-config --datdir)

my_cmd.so: my_cmd.cc
	$(YOSYS)-config --exec --cxx $(subst $(DATDIR),../../../../share,$(CXXFLAGS)) --ldflags -o my_cmd.so -shared my_cmd.cc --ldlibs

test0.log: my_cmd.so
	$(YOSYS) -QTl test0.log_new -m ./my_cmd.so -p 'my_cmd foo bar' -f verilog absval_ref.v
	mv test0.log_new test0.log

test1.log: my_cmd.so
	$(YOSYS) -QTl test1.log_new -m ./my_cmd.so -p 'clean; test1; dump' -f verilog absval_ref.v
	mv test1.log_new test1.log

test1.dot: my_cmd.so
	$(YOSYS) -m ./my_cmd.so -p 'test1; show -format dot -prefix test1'

test2.log: my_cmd.so
	$(YOSYS) -QTl test2.log_new -m ./my_cmd.so -p 'hierarchy -top test; test2' -f verilog sigmap_test.v
	mv test2.log_new test2.log

.PHONY: clean
clean:
	rm -f *.d *.so *.dot
