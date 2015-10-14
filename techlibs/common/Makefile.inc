
ifneq ($(SMALL),1)
OBJS += techlibs/common/synth.o
OBJS += techlibs/common/prep.o
endif

GENFILES += techlibs/common/simlib_help.inc
GENFILES += techlibs/common/simcells_help.inc

techlibs/common/simlib_help.inc: techlibs/common/cellhelp.py techlibs/common/simlib.v
	$(Q) mkdir -p techlibs/common
	$(P) python3 $^ > $@.new
	$(Q) mv $@.new $@

techlibs/common/simcells_help.inc: techlibs/common/cellhelp.py techlibs/common/simcells.v
	$(Q) mkdir -p techlibs/common
	$(P) python3 $^ > $@.new
	$(Q) mv $@.new $@

kernel/register.o: techlibs/common/simlib_help.inc techlibs/common/simcells_help.inc

$(eval $(call add_share_file,share,techlibs/common/simlib.v))
$(eval $(call add_share_file,share,techlibs/common/simcells.v))
$(eval $(call add_share_file,share,techlibs/common/techmap.v))
$(eval $(call add_share_file,share,techlibs/common/pmux2mux.v))
$(eval $(call add_share_file,share,techlibs/common/adff2dff.v))
$(eval $(call add_share_file,share,techlibs/common/cells.lib))

