
OBJS += techlibs/xilinx/synth_xilinx.o

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith.v))

