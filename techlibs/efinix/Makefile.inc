
OBJS += techlibs/efinix/synth_efinix.o

$(eval $(call add_share_file,share/efinix,techlibs/efinix/cells_map.v))
$(eval $(call add_share_file,share/efinix,techlibs/efinix/arith_map.v))
$(eval $(call add_share_file,share/efinix,techlibs/efinix/cells_sim.v))
