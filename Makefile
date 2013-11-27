
CONFIG := clang-debug
# CONFIG := gcc-debug
# CONFIG := release

# features (the more the better)
ENABLE_TCL := 1
ENABLE_QT4 := 1
ENABLE_MINISAT := 1
ENABLE_ABC := 1

# other configuration flags
ENABLE_GPROF := 0

DESTDIR := /usr/local
INSTALL_SUDO :=

OBJS =
GENFILES =
EXTRA_TARGETS =
TARGETS = yosys yosys-config

all: top-all

CXXFLAGS = -Wall -Wextra -ggdb -I"$(shell pwd)" -MD -D_YOSYS_ -fPIC
LDFLAGS = -rdynamic
LDLIBS = -lstdc++ -lreadline -lm -ldl -lrt
QMAKE = qmake-qt4

YOSYS_VER := 0.0.x
GIT_REV := $(shell git rev-parse --short HEAD || echo UNKOWN)
OBJS = kernel/version_$(GIT_REV).o

ABCREV = 766d323095c4
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
CXXFLAGS += -I/usr/include/tcl8.5 -DYOSYS_ENABLE_TCL
LDLIBS += -ltcl8.5
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
include techlibs/*/Makefile.inc

top-all: $(TARGETS) $(EXTRA_TARGETS)

yosys: $(OBJS)
	$(CXX) -o yosys $(LDFLAGS) $(OBJS) $(LDLIBS)

kernel/version_$(GIT_REV).cc: Makefile
	rm -f kernel/version_*.o kernel/version_*.d kernel/version_*.cc
	echo "extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys $(YOSYS_VER) (git sha1 $(GIT_REV))\";" > kernel/version_$(GIT_REV).cc

yosys-config: yosys-config.in
	sed -e 's,@CXX@,$(CXX),;' -e 's,@CXXFLAGS@,$(CXXFLAGS),;' -e 's,@LDFLAGS@,$(LDFLAGS),;' -e 's,@LDLIBS@,$(LDLIBS),;' \
			-e 's,@BINDIR@,$(DESTDIR)/bin,;' -e 's,@DATDIR@,$(DESTDIR)/share/yosys,;' < yosys-config.in > yosys-config
	chmod +x yosys-config

yosys-svgviewer: libs/svgviewer/*.h libs/svgviewer/*.cpp
	cd libs/svgviewer && $(QMAKE) && make
	cp libs/svgviewer/svgviewer yosys-svgviewer

abc:
ifeq ($(ABCPULL),1)
	test -d abc || hg clone https://bitbucket.org/alanmi/abc abc
	cd abc && hg pull && hg update -r $(ABCREV)
endif
	cd abc && $(MAKE)
	cp abc/abc yosys-abc

abc/abc-$(ABCREV):
	if test "`cd abc && hg identify`" != "$(ABCREV)"; then \
		test $(ABCPULL) -ne 0 || { echo; echo "!!! ABC not up to date and ABCPULL set to 0 in Makefile !!!"; echo; exit 1; }; \
		test -d abc || hg clone https://bitbucket.org/alanmi/abc abc; \
		cd abc && hg pull && hg update -r $(ABCREV); \
	fi
	cd abc && $(MAKE)
	cp abc/abc abc/abc-$(ABCREV)

yosys-abc: abc/abc-$(ABCREV)
	cp abc/abc-$(ABCREV) yosys-abc

test: yosys
	cd tests/simple && bash run-test.sh
	cd tests/hana && bash run-test.sh
	cd tests/asicworld && bash run-test.sh

install: $(TARGETS) $(EXTRA_TARGETS)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)/bin
	$(INSTALL_SUDO) install $(TARGETS) $(DESTDIR)/bin/
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)/share/yosys
	$(INSTALL_SUDO) cp -r share/. $(DESTDIR)/share/yosys/.

manual:
	cd manual && bash make.sh

clean:
	rm -rf share
	rm -f $(OBJS) $(GENFILES) $(TARGETS)
	rm -f kernel/version_*.o kernel/version_*.cc
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
	echo 'CONFIG := gcc-debug' > Makefile.conf
	echo 'ENABLE_GPROF := 1' >> Makefile.conf

config-sudo:
	echo "INSTALL_SUDO := sudo" >> Makefile.conf

-include libs/*/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d

.PHONY: all top-all abc test install install-abc manual clean mrproper qtcreator
.PHONY: config-clean config-clang-debug config-gcc-debug config-release

