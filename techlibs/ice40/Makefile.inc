
OBJS += techlibs/ice40/synth_ice40.o
OBJS += techlibs/ice40/ice40_braminit.o
OBJS += techlibs/ice40/ice40_ffssr.o
OBJS += techlibs/ice40/ice40_ffinit.o
OBJS += techlibs/ice40/ice40_opt.o

GENFILES += techlibs/ice40/brams_init1.vh
GENFILES += techlibs/ice40/brams_init2.vh
GENFILES += techlibs/ice40/brams_init3.vh

EXTRA_OBJS += techlibs/ice40/brams_init.mk
.SECONDARY: techlibs/ice40/brams_init.mk

techlibs/ice40/brams_init.mk: techlibs/ice40/brams_init.py
	$(Q) mkdir -p techlibs/ice40
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch techlibs/ice40/brams_init.mk

techlibs/ice40/brams_init1.vh: techlibs/ice40/brams_init.mk
techlibs/ice40/brams_init2.vh: techlibs/ice40/brams_init.mk
techlibs/ice40/brams_init3.vh: techlibs/ice40/brams_init.mk

$(eval $(call add_share_file,share/ice40,techlibs/ice40/arith_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_sim.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/latches_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/brams.txt))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/brams_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/dsp_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/abc9_model.v))

$(eval $(call add_gen_share_file,share/ice40,techlibs/ice40/brams_init1.vh))
$(eval $(call add_gen_share_file,share/ice40,techlibs/ice40/brams_init2.vh))
$(eval $(call add_gen_share_file,share/ice40,techlibs/ice40/brams_init3.vh))

