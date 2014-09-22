
OBJS += techlibs/common/synth.o

EXTRA_TARGETS += techlibs/common/blackbox.v

techlibs/common/blackbox.v: techlibs/common/blackbox.sed techlibs/common/simlib.v techlibs/common/simcells.v
	$(P) cat techlibs/common/simlib.v techlibs/common/simcells.v | $(SED) -rf techlibs/common/blackbox.sed > techlibs/common/blackbox.v.new
	$(Q) mv techlibs/common/blackbox.v.new techlibs/common/blackbox.v

EXTRA_TARGETS += share/simlib.v share/simcells.v share/techmap.v share/blackbox.v share/pmux2mux.v share/adff2dff.v

share/simlib.v: techlibs/common/simlib.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/simlib.v share/simlib.v

share/simcells.v: techlibs/common/simcells.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/simcells.v share/simcells.v

share/techmap.v: techlibs/common/techmap.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/techmap.v share/techmap.v

share/blackbox.v: techlibs/common/blackbox.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/blackbox.v share/blackbox.v

share/pmux2mux.v: techlibs/common/pmux2mux.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/pmux2mux.v share/pmux2mux.v

share/adff2dff.v: techlibs/common/adff2dff.v
	$(P) mkdir -p share
	$(Q) cp techlibs/common/adff2dff.v share/adff2dff.v

