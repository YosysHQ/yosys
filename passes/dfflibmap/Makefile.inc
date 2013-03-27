
OBJS += passes/dfflibmap/dfflibmap.o
OBJS += passes/dfflibmap/libparse.o

TARGETS += yosys-filterlib
GENFILES += passes/dfflibmap/filterlib.o

yosys-filterlib: passes/dfflibmap/filterlib.o
	$(CXX) -o yosys-filterlib $(LDFLAGS) $^ $(LDLIBS)

