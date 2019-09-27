
OBJS += techlibs/gowin/synth_gowin.o
OBJS += techlibs/gowin/determine_init.o


$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_sim.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/arith_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/bram.txt))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/drams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/dram.txt))



$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_init3.vh))

