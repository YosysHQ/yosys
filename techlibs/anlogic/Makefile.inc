
OBJS += techlibs/anlogic/synth_anlogic.o
OBJS += techlibs/anlogic/anlogic_eqn.o
OBJS += techlibs/anlogic/anlogic_fixcarry.o

GENFILES += techlibs/anlogic/brams_init_16.vh
GENFILES += techlibs/anlogic/brams_init_9.vh
GENFILES += techlibs/anlogic/brams_init_8.vh

EXTRA_OBJS += techlibs/anlogic/brams_init.mk
.SECONDARY: techlibs/anlogic/brams_init.mk

techlibs/anlogic/brams_init.mk: techlibs/anlogic/brams_init.py
	$(Q) mkdir -p techlibs/anlogic
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch $@

techlibs/anlogic/brams_init_16.vh: techlibs/anlogic/brams_init.mk
techlibs/anlogic/brams_init_9.vh: techlibs/anlogic/brams_init.mk
techlibs/anlogic/brams_init_8.vh: techlibs/anlogic/brams_init.mk

$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/arith_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/cells_sim.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/eagle_bb.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutrams.txt))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutrams_map.v))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/lutram_init_16x4.vh))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/brams.txt))
$(eval $(call add_share_file,share/anlogic,techlibs/anlogic/brams_map.v))

$(eval $(call add_gen_share_file,share/anlogic,techlibs/anlogic/brams_init_16.vh))
$(eval $(call add_gen_share_file,share/anlogic,techlibs/anlogic/brams_init_9.vh))
$(eval $(call add_gen_share_file,share/anlogic,techlibs/anlogic/brams_init_8.vh))
