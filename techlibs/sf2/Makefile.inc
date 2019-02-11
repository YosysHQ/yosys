
OBJS += techlibs/sf2/synth_sf2.o
OBJS += techlibs/sf2/sf2_iobs.o

$(eval $(call add_share_file,share/sf2,techlibs/sf2/arith_map.v))
$(eval $(call add_share_file,share/sf2,techlibs/sf2/cells_map.v))
$(eval $(call add_share_file,share/sf2,techlibs/sf2/cells_sim.v))

