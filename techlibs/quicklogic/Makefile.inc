OBJS += techlibs/quicklogic/synth_quicklogic.o

GENFILES += techlibs/quicklogic/bram_init_8_16.vh
GENFILES += techlibs/quicklogic/bram_init_32.vh

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/lut_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_sim.v))

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams_map.v))

EXTRA_OBJS += techlibs/quicklogic/brams_init.mk 
.SECONDARY: techlibs/quicklogic/brams_init.mk 

techlibs/quicklogic/brams_init.mk: techlibs/quicklogic/brams_init.py
	$(Q) mkdir -p techlibs/quicklogic
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch $@


techlibs/quicklogic/bram_init_8_16.vh: techlibs/quicklogic/brams_init.mk
techlibs/quicklogic/bram_init_32.vh: techlibs/quicklogic/brams_init.mk

$(eval $(call add_gen_share_file,share/quicklogic,techlibs/quicklogic/bram_init_8_16.vh))
$(eval $(call add_gen_share_file,share/quicklogic,techlibs/quicklogic/bram_init_32.vh))
