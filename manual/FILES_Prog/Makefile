
test: stubnets.so
	yosys -q -l test1.log -m ./stubnets.so test.v -p "proc; stubnets"
	yosys -q -l test2.log -m ./stubnets.so test.v -p "proc; opt; stubnets"
	yosys -q -l test3.log -m ./stubnets.so test.v -p "proc; techmap; opt; stubnets -report_bits"
	tail test1.log test2.log test3.log

stubnets.so: stubnets.cc
	$(shell yosys-config --cxx --cxxflags --ldflags -o stubnets.so -shared stubnets.cc --ldlibs )

clean:
	rm -f test1.log test2.log test3.log
	rm -f stubnets.so stubnets.d

