
CONFIG := clang
# CONFIG := gcc
# CONFIG := gcc-4.6
# CONFIG := emcc

# features (the more the better)
ENABLE_TCL := 1
ENABLE_ABC := 1
ENABLE_PLUGINS := 1
ENABLE_READLINE := 1
ENABLE_VERIFIC := 0

# other configuration flags
ENABLE_GPROF := 0

DESTDIR := /usr/local
INSTALL_SUDO :=

OBJS =
GENFILES =
EXTRA_TARGETS =
TARGETS = yosys yosys-config

PRETTY = 1
SMALL = 0

all: top-all

CXXFLAGS = -Wall -Wextra -ggdb -I"$(shell pwd)" -MD -DYOSYS_SRC='"$(shell pwd)"' -D_YOSYS_ -fPIC -I${DESTDIR}/include
LDFLAGS = -L${DESTDIR}/lib
LDLIBS = -lstdc++ -lm
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

YOSYS_VER := 0.3.0+
GIT_REV := $(shell git rev-parse --short HEAD 2> /dev/null || echo UNKOWN)
OBJS = kernel/version_$(GIT_REV).o

# set 'ABCREV = default' to use abc/ as it is
#
# Note: If you do ABC development, make sure that 'abc' in this directory
# is just a symlink to your actual ABC working directory, as 'make mrproper'
# will remove the 'abc' directory and you do not want to accidentally
# delete your work on ABC..
ABCREV = 4d547a5e065b
ABCPULL = 1

define newline


endef

ifneq ($(wildcard Makefile.conf),)
$(info $(subst $$--$$,$(newline),$(shell sed 's,^,[Makefile.conf] ,; s,$$,$$--$$,;' < Makefile.conf | tr -d '\n' | sed 's,\$$--\$$$$,,')))
include Makefile.conf
endif

ifeq ($(CONFIG),clang)
CXX = clang
CXXFLAGS += -std=c++11 -Os

else ifeq ($(CONFIG),gcc)
CXX = gcc
CXXFLAGS += -std=gnu++0x -Os

else ifeq ($(CONFIG),gcc-4.6)
CXX = gcc-4.6
CXXFLAGS += -std=gnu++0x -Os

else ifeq ($(CONFIG),emcc)
CXX = emcc
CXXFLAGS += -std=c++11 -Os -Wno-warn-absolute-paths
CXXFLAGS := $(filter-out -ggdb,$(CXXFLAGS))

else ifneq ($(CONFIG),none)
$(error Invalid CONFIG setting '$(CONFIG)'. Valid values: clang, gcc, gcc-4.6, emcc, none)
endif

ifeq ($(ENABLE_READLINE),1)
CXXFLAGS += -DYOSYS_ENABLE_READLINE
LDLIBS += -lreadline
endif

ifeq ($(ENABLE_PLUGINS),1)
CXXFLAGS += -DYOSYS_ENABLE_PLUGINS
LDLIBS += -lffi -ldl
endif

ifeq ($(ENABLE_TCL),1)
TCL_VERSION ?= tcl8.5
TCL_INCLUDE ?= /usr/include/$(TCL_VERSION)
CXXFLAGS += -I$(TCL_INCLUDE) -DYOSYS_ENABLE_TCL
LDLIBS += -l$(TCL_VERSION)
endif

ifeq ($(ENABLE_GPROF),1)
CXXFLAGS += -pg
LDFLAGS += -pg
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

ifeq ($(PRETTY), 1)
P_STATUS = 0
P_OFFSET = 0
P_UPDATE = $(eval P_STATUS=$(shell echo $(OBJS) yosys | gawk 'BEGIN { RS = " "; I = $(P_STATUS)+0; } $$1 == "$@" && NR > I { I = NR; } END { print I; }'))
P_SHOW = [$(shell gawk "BEGIN { N=$(words $(OBJS) yosys); printf \"%3d\", $(P_OFFSET)+90*$(P_STATUS)/N; exit; }")%]
P = @echo "$(if $(findstring $@,$(TARGETS) $(EXTRA_TARGETS)),$(eval P_OFFSET = 10))$(call P_UPDATE)$(call P_SHOW) Building $@";
Q = @
S = -s
else
P_SHOW = ->
P =
Q =
S =
endif

OBJS += kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o kernel/yosys.o

OBJS += libs/bigint/BigIntegerAlgorithms.o libs/bigint/BigInteger.o libs/bigint/BigIntegerUtils.o
OBJS += libs/bigint/BigUnsigned.o libs/bigint/BigUnsignedInABase.o

OBJS += libs/sha1/sha1.o

ifneq ($(SMALL),1)

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

else

include frontends/verilog/Makefile.inc
include frontends/ilang/Makefile.inc
include frontends/ast/Makefile.inc

OBJS += passes/hierarchy/hierarchy.o
OBJS += passes/cmds/select.o
OBJS += passes/cmds/show.o
OBJS += passes/cmds/stat.o
OBJS += passes/cmds/cover.o
OBJS += passes/cmds/design.o
OBJS += passes/cmds/plugin.o

include passes/proc/Makefile.inc
include passes/opt/Makefile.inc
include passes/techmap/Makefile.inc
include passes/abc/Makefile.inc

include backends/verilog/Makefile.inc
include backends/ilang/Makefile.inc

include techlibs/common/Makefile.inc

endif

top-all: $(TARGETS) $(EXTRA_TARGETS)
	@echo ""
	@echo "  Build successful."
	@echo ""

yosys: $(OBJS)
	$(P) $(CXX) -o yosys $(LDFLAGS) $(OBJS) $(LDLIBS)

%.o: %.cc
	$(P) $(CXX) -o $@ -c $(CXXFLAGS) $<

%.o: %.cpp
	$(P) $(CXX) -o $@ -c $(CXXFLAGS) $<

kernel/version_$(GIT_REV).cc: Makefile
	$(P) rm -f kernel/version_*.o kernel/version_*.d kernel/version_*.cc
	$(Q) echo "extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys $(YOSYS_VER) (git sha1 $(GIT_REV), $(CXX) ` \
			$(CXX) --version | tr ' ()' '\n' | grep '^[0-9]' | head -n1` $(filter -f% -m% -O% -DNDEBUG,$(CXXFLAGS)))\";" > kernel/version_$(GIT_REV).cc

yosys-config: yosys-config.in
	$(P) $(SED) -e 's,@CXX@,$(CXX),;' -e 's,@CXXFLAGS@,$(CXXFLAGS),;' -e 's,@LDFLAGS@,$(LDFLAGS),;' -e 's,@LDLIBS@,$(LDLIBS),;' \
			-e 's,@BINDIR@,$(DESTDIR)/bin,;' -e 's,@DATDIR@,$(DESTDIR)/share/yosys,;' < yosys-config.in > yosys-config
	$(Q) chmod +x yosys-config

abc/abc-$(ABCREV):
	$(P)
ifneq ($(ABCREV),default)
	$(Q) if ( cd abc 2> /dev/null && hg identify; ) | grep -q +; then \
		echo 'REEBE: NOP pbagnvaf ybpny zbqvsvpngvbaf! Frg NOPERI=qrsnhyg va Lbflf Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; false; \
	fi
	$(Q) if test "`cd abc 2> /dev/null && hg identify | cut -f1 -d' '`" != "$(ABCREV)"; then \
		test $(ABCPULL) -ne 0 || { echo 'REEBE: NOP abg hc gb qngr naq NOPCHYY frg gb 0 va Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; exit 1; }; \
		echo "Pulling ABC from bitbucket.org:"; \
		test -d abc || hg clone https://bitbucket.org/alanmi/abc abc; \
		cd abc && hg pull && hg update -r $(ABCREV); \
	fi
endif
	$(Q) rm -f abc/abc-[0-9a-f]*
	$(Q) cd abc && $(MAKE) $(S) PROG="abc-$(ABCREV)" MSG_PREFIX="$(eval P_OFFSET = 5)$(call P_SHOW)$(eval P_OFFSET = 10) ABC: "

ifeq ($(ABCREV),default)
.PHONY: abc/abc-$(ABCREV)
endif

yosys-abc: abc/abc-$(ABCREV)
	$(P) cp abc/abc-$(ABCREV) yosys-abc

test: $(TARGETS) $(EXTRA_TARGETS)
	+cd tests/simple && bash run-test.sh
	+cd tests/hana && bash run-test.sh
	+cd tests/asicworld && bash run-test.sh
	+cd tests/realmath && bash run-test.sh
	+cd tests/share && bash run-test.sh
	+cd tests/fsm && bash run-test.sh
	+cd tests/techmap && bash run-test.sh
	+cd tests/memories && bash run-test.sh
	+cd tests/various && bash run-test.sh
	+cd tests/sat && bash run-test.sh
	@echo ""
	@echo "  Passed \"make test\"."
	@echo ""

VALGRIND ?= valgrind --error-exitcode=1 --leak-check=full --show-reachable=yes --errors-for-leak-kinds=all

vgtest: $(TARGETS) $(EXTRA_TARGETS)
	$(VALGRIND) ./yosys -p 'setattr -mod -unset top; hierarchy; proc; opt; memory -nomap; opt -fine; techmap; opt' $$( ls tests/simple/*.v | grep -v repwhile.v )
	@echo ""
	@echo "  Passed \"make vgtest\"."
	@echo ""

vloghtb: $(TARGETS) $(EXTRA_TARGETS)
	+cd tests/vloghtb && bash run-test.sh
	@echo ""
	@echo "  Passed \"make vloghtb\"."
	@echo ""

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

clean-abc:
	make -C abc clean
	rm -f yosys-abc abc/abc-[0-9a-f]*

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

config-clang: clean
	echo 'CONFIG := clang' > Makefile.conf

config-gcc: clean
	echo 'CONFIG := gcc' > Makefile.conf

config-gcc-4.6: clean
	echo 'CONFIG := gcc-4.6' > Makefile.conf

config-emcc: clean
	echo 'CONFIG := emcc' > Makefile.conf
	echo 'ENABLE_TCL := 0' >> Makefile.conf
	echo 'ENABLE_ABC := 0' >> Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf
	echo 'ENABLE_READLINE := 0' >> Makefile.conf

config-gprof: clean
	echo 'CONFIG := gcc' > Makefile.conf
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
.PHONY: config-clean config-clang config-gcc config-gcc-4.6 config-gprof config-sudo

