
ifneq ($(SMALL),1)
OBJS += techlibs/common/synth.o
endif

$(eval $(call add_share_file,share,techlibs/common/simlib.v))
$(eval $(call add_share_file,share,techlibs/common/simcells.v))
$(eval $(call add_share_file,share,techlibs/common/techmap.v))
$(eval $(call add_share_file,share,techlibs/common/pmux2mux.v))
$(eval $(call add_share_file,share,techlibs/common/adff2dff.v))
$(eval $(call add_share_file,share,techlibs/common/cells.lib))

