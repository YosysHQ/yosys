
OBJS += techlibs/quicklogic/synth_quicklogic.o

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
