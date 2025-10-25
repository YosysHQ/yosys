
OBJS += techlibs/gowin/synth_gowin.o

$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_sim.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_xtra_gw1n.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_xtra_gw2a.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_xtra_gw5a.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/arith_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_map_gw5a.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams.txt))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/lutrams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/lutrams.txt))
