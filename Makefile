
CONFIG := clang-debug
# CONFIG := gcc-debug
# CONFIG := release

# features (the more the better)
ENABLE_TCL := 1
ENABLE_QT4 := 1
ENABLE_ABC := 1
ENABLE_VERIFIC := 0

# other configuration flags
ENABLE_GPROF := 0

DESTDIR := /usr/local
INSTALL_SUDO :=

OBJS =
GENFILES =
EXTRA_TARGETS =
TARGETS = yosys yosys-config

all: top-all

CXXFLAGS = -Wall -Wextra -ggdb -I"$(shell pwd)" -MD -D_YOSYS_ -fPIC -I${DESTDIR}/include
LDFLAGS = -L${DESTDIR}/lib
LDLIBS = -lstdc++ -lreadline -lm -ldl
QMAKE = qmake-qt4
SED = sed

ifeq (Darwin,$(findstring Darwin,$(shell uname)))
	# add macports include and library path to search directories, don't use '-rdynamic' and '-lrt':
	CXXFLAGS += -I/opt/local/include
	LDFLAGS += -L/opt/local/lib
	QMAKE = qmake
	SED = gsed
else
	LDFLAGS += -rdynamic
	LDLIBS += -lrt
endif

YOSYS_VER := 0.2.0+
GIT_REV := $(shell git rev-parse --short HEAD || echo UNKOWN)
OBJS = kernel/version_$(GIT_REV).o

# set 'ABCREV = default' to use abc/ as it is
#
# Note: If you do ABC development, make sure that 'abc' in this directory
# is just a symlink to your actual ABC working directory, as 'make mrproper'
# will remove the 'abc' directory and you do not want to accidentally
# delete your work on ABC..
ABCREV = 7600ffb9340c
ABCPULL = 1

-include Makefile.conf

ifeq ($(CONFIG),clang-debug)
CXX = clang
CXXFLAGS += -std=c++11 -Os
endif

ifeq ($(CONFIG),gcc-debug)
CXX = gcc
CXXFLAGS += -std=gnu++0x -Os
endif

ifeq ($(CONFIG),release)
CXX = gcc
CXXFLAGS += -std=gnu++0x -march=native -O3 -DNDEBUG
endif

ifeq ($(ENABLE_TCL),1)
TCL_VERSION ?= tcl8.5
TCL_INCLUDE ?= /usr/include/$(TCL_VERSION)
CXXFLAGS += -I$(TCL_INCLUDE) -DYOSYS_ENABLE_TCL
LDLIBS += -l$(TCL_VERSION)
endif

ifeq ($(ENABLE_GPROF),1)
CXXFLAGS += -pg -fno-inline
LDFLAGS += -pg
endif

ifeq ($(ENABLE_QT4),1)
TARGETS += yosys-svgviewer
endif

ifeq ($(ENABLE_ABC),1)
TARGETS += yosys-abc
endif

ifeq ($(ENABLE_VERIFIC),1)
VERIFIC_DIR ?= /usr/local/src/verific_lib_eval
VERIFIC_COMPONENTS ?= verilog vhdl database util containers
CXXFLAGS += $(patsubst %,-I$(VERIFIC_DIR)/%,$(VERIFIC_COMPONENTS)) -DYOSYS_ENABLE_VERIFIC
LDLIBS += $(patsubst %,$(VERIFIC_DIR)/%/*-linux.a,$(VERIFIC_COMPONENTS))
endif

OBJS += kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o
OBJS += kernel/compatibility.o

OBJS += libs/bigint/BigIntegerAlgorithms.o libs/bigint/BigInteger.o libs/bigint/BigIntegerUtils.o
OBJS += libs/bigint/BigUnsigned.o libs/bigint/BigUnsignedInABase.o

OBJS += libs/sha1/sha1.o
OBJS += libs/subcircuit/subcircuit.o

OBJS += libs/ezsat/ezsat.o
OBJS += libs/ezsat/ezminisat.o

OBJS += libs/minisat/Options.o
OBJS += libs/minisat/SimpSolver.o
OBJS += libs/minisat/Solver.o
OBJS += libs/minisat/System.o

include frontends/*/Makefile.inc
include passes/*/Makefile.inc
include backends/*/Makefile.inc
include techlibs/*/Makefile.inc

top-all: $(TARGETS) $(EXTRA_TARGETS)

yosys: $(OBJS)
	$(CXX) -o yosys $(LDFLAGS) $(OBJS) $(LDLIBS)

kernel/version_$(GIT_REV).cc: Makefile
	rm -f kernel/version_*.o kernel/version_*.d kernel/version_*.cc
	echo "extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys $(YOSYS_VER) (git sha1 $(GIT_REV))\";" > kernel/version_$(GIT_REV).cc

yosys-config: yosys-config.in
	$(SED) -e 's,@CXX@,$(CXX),;' -e 's,@CXXFLAGS@,$(CXXFLAGS),;' -e 's,@LDFLAGS@,$(LDFLAGS),;' -e 's,@LDLIBS@,$(LDLIBS),;' \
			-e 's,@BINDIR@,$(DESTDIR)/bin,;' -e 's,@DATDIR@,$(DESTDIR)/share/yosys,;' < yosys-config.in > yosys-config
	chmod +x yosys-config

yosys-svgviewer: libs/svgviewer/*.h libs/svgviewer/*.cpp
	cd libs/svgviewer && $(QMAKE) && make
	cp `find libs/svgviewer -name svgviewer -type f` yosys-svgviewer

abc/abc-$(ABCREV):
ifneq ($(ABCREV),default)
	if ( cd abc && hg identify; ) | grep -q +; then \
		echo 'REEBE: NOP pbagnvaf ybpny zbqvsvpngvbaf! Frg NOPERI=qrsnhyg va Lbflf Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; false; \
	fi
	if test "`cd abc && hg identify | cut -f1 -d' '`" != "$(ABCREV)"; then \
		test $(ABCPULL) -ne 0 || { echo 'REEBE: NOP abg hc gb qngr naq NOPCHYY frg gb 0 va Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; exit 1; }; \
		test -d abc || hg clone https://bitbucket.org/alanmi/abc abc; \
		cd abc && hg pull && hg update -r $(ABCREV); \
	fi
endif
	rm -f abc/abc-[0-9a-f]*
	cd abc && $(MAKE) PROG="abc-$(ABCREV)" MSG_PREFIX="YOSYS-ABC: "

ifeq ($(ABCREV),default)
.PHONY: abc/abc-$(ABCREV)
endif

yosys-abc: abc/abc-$(ABCREV)
	cp abc/abc-$(ABCREV) yosys-abc

test: $(TARGETS) $(EXTRA_TARGETS)
	cd tests/simple && bash run-test.sh
	cd tests/hana && bash run-test.sh
	cd tests/asicworld && bash run-test.sh
	cd tests/techmap && bash run-test.sh
	cd tests/sat && bash run-test.sh

install: $(TARGETS) $(EXTRA_TARGETS)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)/bin
	$(INSTALL_SUDO) install $(TARGETS) $(DESTDIR)/bin/
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)/share/yosys
	$(INSTALL_SUDO) cp -r share/. $(DESTDIR)/share/yosys/.

manual: $(TARGETS) $(EXTRA_TARGETS)
	cd manual && bash appnotes.sh
	cd manual && bash presentation.sh
	cd manual && bash manual.sh

clean:
	rm -rf share
	cd manual && bash clean.sh
	rm -f $(OBJS) $(GENFILES) $(TARGETS) $(EXTRA_TARGETS)
	rm -f kernel/version_*.o kernel/version_*.cc abc/abc-[0-9a-f]*
	rm -f libs/*/*.d frontends/*/*.d passes/*/*.d backends/*/*.d kernel/*.d techlibs/*/*.d
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
	echo 'CONFIG := gcc-debug' > Makefile.conf
	echo 'ENABLE_GPROF := 1' >> Makefile.conf

config-sudo:
	echo "INSTALL_SUDO := sudo" >> Makefile.conf

-include libs/*/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d
-include techlibs/*/*.d

.PHONY: all top-all abc test install install-abc manual clean mrproper qtcreator
.PHONY: config-clean config-clang-debug config-gcc-debug config-release

