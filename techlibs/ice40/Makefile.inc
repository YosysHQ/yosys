
OBJS += techlibs/ice40/synth_ice40.o

$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_sim.v))

