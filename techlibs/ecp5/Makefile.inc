
OBJS += techlibs/ecp5/synth_ecp5.o

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_sim.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/drams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/dram.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/bram.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/arith_map.v))

EXTRA_OBJS += techlibs/ecp5/brams_init.mk
.SECONDARY: techlibs/ecp5/brams_init.mk

techlibs/ecp5/brams_init.mk: techlibs/ecp5/brams_init.py
	$(Q) mkdir -p techlibs/ecp5
	$(P) python3 $<
	$(Q) touch $@

techlibs/ecp5/bram_init_1_2_4.vh: techlibs/ecp5/brams_init.mk
techlibs/ecp5/bram_init_9_18_36.vh: techlibs/ecp5/brams_init.mk

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/bram_init_1_2_4.vh))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/bram_init_9_18_36.vh))
