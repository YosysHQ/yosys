ifeq ($(ENABLE_PROTOBUF),1)

backends/protobuf/yosys.pb.cc backends/protobuf/yosys.pb.h: misc/yosys.proto
	$(Q) cd misc && protoc --cpp_out "../backends/protobuf" yosys.proto

OBJS += backends/protobuf/protobuf.o backends/protobuf/yosys.pb.o

endif
