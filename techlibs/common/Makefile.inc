
EXTRA_TARGETS += techlibs/common/blackbox.v

techlibs/common/blackbox.v: techlibs/common/blackbox.sed techlibs/common/simlib.v techlibs/common/simcells.v
	cat techlibs/common/simlib.v techlibs/common/simcells.v | sed -rf techlibs/common/blackbox.sed > techlibs/common/blackbox.v.new
	mv techlibs/common/blackbox.v.new techlibs/common/blackbox.v

EXTRA_TARGETS += share/simlib.v share/simcells.v share/blackbox.v

share/simlib.v: techlibs/common/simlib.v
	mkdir -p share
	cp techlibs/common/simlib.v share/simlib.v

share/simcells.v: techlibs/common/simcells.v
	mkdir -p share
	cp techlibs/common/simcells.v share/simcells.v

share/blackbox.v: techlibs/common/blackbox.v
	mkdir -p share
	cp techlibs/common/blackbox.v share/blackbox.v

