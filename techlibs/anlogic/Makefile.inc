
OBJS += techlibs/anlogic/synth_anlogic.o
OBJS += techlibs/anlogic/anlogic_eqn.o
OBJS += techlibs/anlogic/anlogic_fixcarry.o

$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/arith_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_sim.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/eagle_bb.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutrams.txt))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutrams_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutram_init_16x4.vh))
