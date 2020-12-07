OBJS += techlibs/nexus/synth_nexus.o

$(eval $(call add_share_file,share/nexus,techlibs/nexus/cells_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/cells_sim.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/parse_init.vh))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/cells_xtra.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/lutrams_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/lutrams.txt))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/brams_init.vh))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/brams_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/brams.txt))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/lrams_init.vh))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/lrams_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/lrams.txt))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/arith_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/latches_map.v))
$(eval $(call add_share_file,share/nexus,techlibs/nexus/dsp_map.v))

