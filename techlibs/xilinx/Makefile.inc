
OBJS += techlibs/xilinx/synth_xilinx.o

EXTRA_TARGETS += share/xilinx/cells.v

share/xilinx/cells.v: techlibs/xilinx/cells.v
	$(P) mkdir -p share/xilinx
	$(Q) cp techlibs/xilinx/cells.v share/xilinx/cells.v

