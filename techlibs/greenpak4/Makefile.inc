
OBJS += techlibs/greenpak4/synth_greenpak4.o
OBJS += techlibs/greenpak4/greenpak4_dffinv.o

$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_blackbox.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_latch.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_map.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_sim.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_sim_ams.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_sim_digital.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_sim_wip.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/gp_dff.lib))
