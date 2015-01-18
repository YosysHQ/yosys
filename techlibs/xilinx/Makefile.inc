
OBJS += techlibs/xilinx/synth_xilinx.o

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith_map.v))

