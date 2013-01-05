
TARGETS += techlibs/blackbox.v

techlibs/blackbox.v: techlibs/blackbox.sed techlibs/simlib.v techlibs/stdcells_sim.v
	cat techlibs/simlib.v techlibs/stdcells_sim.v | sed -rf techlibs/blackbox.sed > techlibs/blackbox.v.new
	mv techlibs/blackbox.v.new techlibs/blackbox.v

