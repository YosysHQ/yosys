
OBJS += techlibs/gowin/synth_gowin.o

$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_sim.v))

