
EXTRA_TARGETS += techlibs/common/blackbox.v

techlibs/common/blackbox.v: techlibs/common/blackbox.sed techlibs/common/simlib.v techlibs/common/stdcells_sim.v
	cat techlibs/common/simlib.v techlibs/common/stdcells_sim.v | sed -rf techlibs/common/blackbox.sed > techlibs/common/blackbox.v.new
	mv techlibs/common/blackbox.v.new techlibs/common/blackbox.v

