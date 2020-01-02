
OBJS += techlibs/gowin/synth_gowin.o
OBJS += techlibs/gowin/determine_init.o


$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/cells_sim.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/arith_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams.txt))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/lutrams_map.v))
$(eval $(call add_share_file,share/gowin,techlibs/gowin/lutrams.txt))



$(eval $(call add_share_file,share/gowin,techlibs/gowin/brams_init3.vh))

EXTRA_OBJS += techlibs/gowin/brams_init.mk
.SECONDARY: techlibs/gowin/brams_init.mk

techlibs/gowin/brams_init.mk: techlibs/gowin/brams_init.py
	$(Q) mkdir -p techlibs/gowin
	$(P) python3 $<
	$(Q) touch $@

techlibs/gowin/bram_init_16.vh: techlibs/gowin/brams_init.mk
$(eval $(call add_gen_share_file,share/gowin,techlibs/gowin/bram_init_16.vh))
