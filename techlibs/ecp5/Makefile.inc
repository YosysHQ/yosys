
OBJS += techlibs/ecp5/synth_ecp5.o

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_sim.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/drams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/dram.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/arith_map.v))
