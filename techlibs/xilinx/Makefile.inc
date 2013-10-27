
OBJS += techlibs/xilinx/synth_xilinx.o

EXTRA_TARGETS += share/xilinx/cells.v

share/xilinx/cells.v: techlibs/xilinx/cells.v
	mkdir -p share/xilinx
	cp techlibs/xilinx/cells.v share/xilinx/cells.v

