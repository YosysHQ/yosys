
all: test0.log test1.log test2.log

my_cmd.so: my_cmd.cc
	../../yosys-config --exec --cxx --cxxflags --ldflags -o my_cmd.so -shared my_cmd.cc --ldlibs

test0.log: my_cmd.so
	../../yosys -Ql test0.log_new -m ./my_cmd.so -p 'my_cmd foo bar' absval_ref.v
	mv test0.log_new test0.log

test1.log: my_cmd.so
	../../yosys -Ql test1.log_new -m ./my_cmd.so -p 'clean; test1; dump' absval_ref.v
	mv test1.log_new test1.log

test2.log: my_cmd.so
	../../yosys -Ql test2.log_new -m ./my_cmd.so -p 'test2' sigmap_test.v
	mv test2.log_new test2.log

