
OBJS += passes/dfflibmap/dfflibmap.o
OBJS += passes/dfflibmap/libparse.o

TARGETS += filterlib
GENFILES += passes/dfflibmap/filterlib.o

filterlib: passes/dfflibmap/filterlib.o
	$(CXX) -o filterlib $(LDFLAGS) $^ $(LDLIBS)

