
OBJS += techlibs/greenpak4/synth_greenpak4.o

$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_map.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/cells_sim.v))
$(eval $(call add_share_file,share/greenpak4,techlibs/greenpak4/gp_dff.lib))
