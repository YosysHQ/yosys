
OBJS += techlibs/ecp5/synth_ecp5.o techlibs/ecp5/ecp5_gsr.o

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_ff.vh))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_io.vh))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_sim.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_bb.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/lutrams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/lutrams.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/brams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/brams.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/arith_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/latches_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/dsp_map.v))
