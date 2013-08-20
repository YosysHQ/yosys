
CONFIG := clang-debug
# CONFIG := gcc-debug
# CONFIG := release

ENABLE_TCL := 1
ENABLE_QT4 := 1
ENABLE_MINISAT := 1
ENABLE_GPROF := 0

OBJS =
GENFILES =
EXTRA_TARGETS =
TARGETS = yosys yosys-config

all: top-all

CXXFLAGS = -Wall -Wextra -ggdb -I"$(shell pwd)" -MD -D_YOSYS_ -fPIC
LDFLAGS = -rdynamic
LDLIBS = -lstdc++ -lreadline -lm -ldl
QMAKE = qmake-qt4

-include Makefile.conf

ifeq ($(CONFIG),clang-debug)
CXX = clang
CXXFLAGS += -std=c++11 -O0
endif

ifeq ($(CONFIG),gcc-debug)
CXX = gcc
CXXFLAGS += -std=gnu++0x -O0
endif

ifeq ($(CONFIG),release)
CXX = gcc
CXXFLAGS += -std=gnu++0x -march=native -O3 -DNDEBUG
endif

ifeq ($(ENABLE_TCL),1)
CXXFLAGS += -I/usr/include/tcl8.5 -DYOSYS_ENABLE_TCL
LDLIBS += -ltcl8.5
endif

ifeq ($(ENABLE_GPROF),1)
CXXFLAGS += -pg
LDFLAGS += -pg
endif

ifeq ($(ENABLE_QT4),1)
TARGETS += yosys-svgviewer
endif

OBJS += kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o

OBJS += libs/bigint/BigIntegerAlgorithms.o libs/bigint/BigInteger.o libs/bigint/BigIntegerUtils.o
OBJS += libs/bigint/BigUnsigned.o libs/bigint/BigUnsignedInABase.o

OBJS += libs/sha1/sha1.o
OBJS += libs/subcircuit/subcircuit.o
OBJS += libs/ezsat/ezsat.o

ifeq ($(ENABLE_MINISAT),1)
CXXFLAGS += -DYOSYS_ENABLE_MINISAT
OBJS += libs/ezsat/ezminisat.o
LDLIBS += -lminisat
endif

include frontends/*/Makefile.inc
include passes/*/Makefile.inc
include backends/*/Makefile.inc
include techlibs/Makefile.inc

top-all: $(TARGETS) $(EXTRA_TARGETS)

yosys: $(OBJS)
	$(CXX) -o yosys $(LDFLAGS) $(OBJS) $(LDLIBS)

yosys-config: yosys-config.in
	sed 's,@CXX@,$(CXX),; s,@CXXFLAGS@,$(CXXFLAGS),; s,@LDFLAGS@,$(LDFLAGS),; s,@LDLIBS@,$(LDLIBS),;' < yosys-config.in > yosys-config
	chmod +x yosys-config

yosys-svgviewer: libs/svgviewer/*.h libs/svgviewer/*.cpp
	cd libs/svgviewer && $(QMAKE) && make
	cp libs/svgviewer/svgviewer yosys-svgviewer

abc:
	test -d abc || hg clone https://bitbucket.org/alanmi/abc abc
	cd abc && hg pull && hg update && make
	cp abc/abc yosys-abc

test: yosys
	cd tests/simple && bash run-test.sh
	cd tests/hana && bash run-test.sh
	cd tests/asicworld && bash run-test.sh

install: $(TARGETS)
	install $(TARGETS) /usr/local/bin/

install-abc:
	install yosys-abc /usr/local/bin/

manual:
	cd manual && bash make.sh

clean:
	rm -f $(OBJS) $(GENFILES) $(TARGETS)
	rm -f libs/*/*.d frontends/*/*.d passes/*/*.d backends/*/*.d kernel/*.d
	cd manual && rm -f *.aux *.bbl *.blg *.idx *.log *.out *.pdf *.toc
	test ! -f libs/svgviewer/Makefile || make -C libs/svgviewer distclean

mrproper: clean
	git clean -xdf

qtcreator:
	{ for file in $(basename $(OBJS)); do \
		for prefix in cc y l; do if [ -f $${file}.$${prefix} ]; then echo $$file.$${prefix}; fi; done \
	done; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \); } > qtcreator.files
	{ echo .; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \) -printf '%h\n' | sort -u; } > qtcreator.includes
	touch qtcreator.config qtcreator.creator

config-clean: clean
	rm -f Makefile.conf

config-clang-debug: clean
	echo 'CONFIG := clang-debug' > Makefile.conf

config-gcc-debug: clean
	echo 'CONFIG := gcc-debug' > Makefile.conf

config-release: clean
	echo 'CONFIG := release' > Makefile.conf

config-gprof: clean
	echo 'CONFIG := release' > Makefile.conf
	echo 'ENABLE_GPROF := 1' >> Makefile.conf

-include libs/*/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d

.PHONY: all top-all abc test install install-abc manual clean mrproper qtcreator
.PHONY: config-clean config-clang-debug config-gcc-debug config-release

