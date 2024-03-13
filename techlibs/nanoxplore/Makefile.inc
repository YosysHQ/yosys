
OBJS += techlibs/nanoxplore/synth_nanoxplore.o

# Techmap
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/arith_map.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_bb.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_bb_l.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_bb_m.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_bb_u.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_map.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_sim.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_wrap.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_wrap_l.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_wrap_m.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/cells_wrap_u.v))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/drams.txt))
$(eval $(call add_share_file,share/nanoxplore,techlibs/nanoxplore/io_map.v))
