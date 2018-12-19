
OBJS += techlibs/anlogic/synth_anlogic.o
OBJS += techlibs/anlogic/anlogic_eqn.o
OBJS += techlibs/anlogic/anlogic_determine_init.o

$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/arith_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_sim.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/eagle_bb.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/drams.txt))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/drams_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/dram_init_16x4.vh))
