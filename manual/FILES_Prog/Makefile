test: stubnets.so
	yosys -ql test1.log -m ./stubnets.so test.v -p "stubnets"
	yosys -ql test2.log -m ./stubnets.so test.v -p "opt; stubnets"
	yosys -ql test3.log -m ./stubnets.so test.v -p "techmap; opt; stubnets -report_bits"
	tail test1.log test2.log test3.log

stubnets.so: stubnets.cc
	yosys-config --exec --cxx --cxxflags --ldflags -o $@ -shared $^ --ldlibs

clean:
	rm -f test1.log test2.log test3.log
	rm -f stubnets.so stubnets.d
