
ifneq ($(SMALL),1)
OBJS += techlibs/common/synth.o
endif

EXTRA_TARGETS += techlibs/common/blackbox.v

techlibs/common/blackbox.v: techlibs/common/blackbox.sed techlibs/common/simlib.v techlibs/common/simcells.v
	$(P) cat techlibs/common/simlib.v techlibs/common/simcells.v | $(SED) -rf techlibs/common/blackbox.sed > techlibs/common/blackbox.v.new
	$(Q) mv techlibs/common/blackbox.v.new techlibs/common/blackbox.v

$(eval $(call add_share_file,share,techlibs/common/simlib.v))
$(eval $(call add_share_file,share,techlibs/common/simcells.v))
$(eval $(call add_share_file,share,techlibs/common/techmap.v))
$(eval $(call add_share_file,share,techlibs/common/blackbox.v))
$(eval $(call add_share_file,share,techlibs/common/pmux2mux.v))
$(eval $(call add_share_file,share,techlibs/common/adff2dff.v))
$(eval $(call add_share_file,share,techlibs/common/cells.lib))

