
OBJS += techlibs/xilinx/synth_xilinx.o

EXTRA_TARGETS += share/xilinx/cells.v share/xilinx/brams.txt share/xilinx/brams.v

share/xilinx/cells.v: techlibs/xilinx/cells.v
	$(P) mkdir -p share/xilinx
	$(Q) cp techlibs/xilinx/cells.v share/xilinx/cells.v

share/xilinx/brams.txt: techlibs/xilinx/brams.txt
	$(P) mkdir -p share/xilinx
	$(Q) cp techlibs/xilinx/brams.txt share/xilinx/brams.txt

share/xilinx/brams.v: techlibs/xilinx/brams.v
	$(P) mkdir -p share/xilinx
	$(Q) cp techlibs/xilinx/brams.v share/xilinx/brams.v

