
CONFIG := clang
# CONFIG := gcc
# CONFIG := gcc-4.8
# CONFIG := afl-gcc
# CONFIG := emcc
# CONFIG := mxe
# CONFIG := msys2
# CONFIG := msys2-64

# features (the more the better)
ENABLE_TCL := 1
ENABLE_ABC := 1
ENABLE_GLOB := 1
ENABLE_PLUGINS := 1
ENABLE_READLINE := 1
ENABLE_EDITLINE := 0
ENABLE_VERIFIC := 0
ENABLE_COVER := 1
ENABLE_LIBYOSYS := 0
ENABLE_PROTOBUF := 0

# python wrappers
ENABLE_PYOSYS := 0

# other configuration flags
ENABLE_GCOV := 0
ENABLE_GPROF := 0
ENABLE_DEBUG := 0
ENABLE_NDEBUG := 0
LINK_CURSES := 0
LINK_TERMCAP := 0
LINK_ABC := 0
# Needed for environments that don't have proper thread support (i.e. emscripten)
DISABLE_ABC_THREADS := 0

# clang sanitizers
SANITIZER =
# SANITIZER = address
# SANITIZER = memory
# SANITIZER = undefined
# SANITIZER = cfi


OS := $(shell uname -s)
PREFIX ?= /usr/local
INSTALL_SUDO :=

ifneq ($(wildcard Makefile.conf),)
include Makefile.conf
endif

BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib
DATDIR := $(PREFIX)/share/yosys

EXE =
OBJS =
GENFILES =
EXTRA_OBJS =
EXTRA_TARGETS =
TARGETS = yosys$(EXE) yosys-config

PRETTY = 1
SMALL = 0

# Unit test
UNITESTPATH := tests/unit

all: top-all

YOSYS_SRC := $(dir $(firstword $(MAKEFILE_LIST)))
VPATH := $(YOSYS_SRC)

CXXFLAGS := $(CXXFLAGS) -Wall -Wextra -ggdb -I. -I"$(YOSYS_SRC)" -MD -D_YOSYS_ -fPIC -I$(PREFIX)/include
LDFLAGS := $(LDFLAGS) -L$(LIBDIR)
LDLIBS := $(LDLIBS) -lstdc++ -lm
PLUGIN_LDFLAGS :=

PKG_CONFIG ?= pkg-config
SED ?= sed
BISON ?= bison
STRIP ?= strip
AWK ?= awk

ifeq ($(OS), Darwin)
PLUGIN_LDFLAGS += -undefined dynamic_lookup

# homebrew search paths
ifneq ($(shell which brew),)
BREW_PREFIX := $(shell brew --prefix)/opt
$(info $$BREW_PREFIX is [${BREW_PREFIX}])
ifeq ($(ENABLE_PYOSYS),1)
CXXFLAGS += -I$(BREW_PREFIX)/boost/include/boost
LDFLAGS += -L$(BREW_PREFIX)/boost/lib
endif
CXXFLAGS += -I$(BREW_PREFIX)/readline/include
LDFLAGS += -L$(BREW_PREFIX)/readline/lib
PKG_CONFIG_PATH := $(BREW_PREFIX)/libffi/lib/pkgconfig:$(PKG_CONFIG_PATH)
PKG_CONFIG_PATH := $(BREW_PREFIX)/tcl-tk/lib/pkgconfig:$(PKG_CONFIG_PATH)
export PATH := $(BREW_PREFIX)/bison/bin:$(BREW_PREFIX)/gettext/bin:$(BREW_PREFIX)/flex/bin:$(PATH)

# macports search paths
else ifneq ($(shell which port),)
PORT_PREFIX := $(patsubst %/bin/port,%,$(shell which port))
CXXFLAGS += -I$(PORT_PREFIX)/include
LDFLAGS += -L$(PORT_PREFIX)/lib
PKG_CONFIG_PATH := $(PORT_PREFIX)/lib/pkgconfig:$(PKG_CONFIG_PATH)
export PATH := $(PORT_PREFIX)/bin:$(PATH)
endif

else
LDFLAGS += -rdynamic
LDLIBS += -lrt
endif

YOSYS_VER := 0.9
GIT_REV := $(shell cd $(YOSYS_SRC) && git rev-parse --short HEAD 2> /dev/null || echo UNKNOWN)
OBJS = kernel/version_$(GIT_REV).o

# set 'ABCREV = default' to use abc/ as it is
#
# Note: If you do ABC development, make sure that 'abc' in this directory
# is just a symlink to your actual ABC working directory, as 'make mrproper'
# will remove the 'abc' directory and you do not want to accidentally
# delete your work on ABC..
ABCREV = 3709744
ABCPULL = 1
ABCURL ?= https://github.com/berkeley-abc/abc
ABCMKARGS = CC="$(CXX)" CXX="$(CXX)" ABC_USE_LIBSTDCXX=1

# set ABCEXTERNAL = <abc-command> to use an external ABC instance
# Note: The in-tree ABC (yosys-abc) will not be installed when ABCEXTERNAL is set.
ABCEXTERNAL ?=

define newline


endef

ifneq ($(wildcard Makefile.conf),)
$(info $(subst $$--$$,$(newline),$(shell sed 's,^,[Makefile.conf] ,; s,$$,$$--$$,;' < Makefile.conf | tr -d '\n' | sed 's,\$$--\$$$$,,')))
include Makefile.conf
endif

ifeq ($(ENABLE_PYOSYS),1)
PYTHON_VERSION_TESTCODE := "import sys;t='{v[0]}.{v[1]}'.format(v=list(sys.version_info[:2]));print(t)"
PYTHON_EXECUTABLE := $(shell if python3 -c ""; then echo "python3"; else echo "python"; fi)
PYTHON_VERSION := $(shell $(PYTHON_EXECUTABLE) -c ""$(PYTHON_VERSION_TESTCODE)"")
PYTHON_MAJOR_VERSION := $(shell echo $(PYTHON_VERSION) | cut -f1 -d.)
PYTHON_PREFIX := $(shell $(PYTHON_EXECUTABLE)-config --prefix)
PYTHON_DESTDIR := $(PYTHON_PREFIX)/lib/python$(PYTHON_VERSION)/site-packages

# Reload Makefile.conf to override python specific variables if defined
ifneq ($(wildcard Makefile.conf),)
include Makefile.conf
endif

endif

ifeq ($(CONFIG),clang)
CXX = clang
LD = clang++
CXXFLAGS += -std=c++11 -Os
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H"

ifneq ($(SANITIZER),)
$(info [Clang Sanitizer] $(SANITIZER))
CXXFLAGS += -g -O1 -fno-omit-frame-pointer -fno-optimize-sibling-calls -fsanitize=$(SANITIZER)
LDFLAGS += -g -fsanitize=$(SANITIZER)
ifeq ($(SANITIZER),address)
ENABLE_COVER := 0
endif
ifeq ($(SANITIZER),memory)
CXXFLAGS += -fPIE -fsanitize-memory-track-origins
LDFLAGS += -fPIE -fsanitize-memory-track-origins
endif
ifeq ($(SANITIZER),cfi)
CXXFLAGS += -flto
LDFLAGS += -flto
endif
endif

else ifeq ($(CONFIG),gcc)
CXX = gcc
LD = gcc
CXXFLAGS += -std=c++11 -Os
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H"

else ifeq ($(CONFIG),gcc-static)
LD = $(CXX)
LDFLAGS := $(filter-out -rdynamic,$(LDFLAGS)) -static
LDLIBS := $(filter-out -lrt,$(LDLIBS))
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
CXXFLAGS += -std=c++11 -Os
ABCMKARGS = CC="$(CC)" CXX="$(CXX)" LD="$(LD)" ABC_USE_LIBSTDCXX=1 LIBS="-lm -lpthread -static" OPTFLAGS="-O" \
                       ARCHFLAGS="-DABC_USE_STDINT_H -DABC_NO_DYNAMIC_LINKING=1 -Wno-unused-but-set-variable $(ARCHFLAGS)" ABC_USE_NO_READLINE=1
ifeq ($(DISABLE_ABC_THREADS),1)
ABCMKARGS += "ABC_USE_NO_PTHREADS=1"
endif

else ifeq ($(CONFIG),gcc-4.8)
CXX = gcc-4.8
LD = gcc-4.8
CXXFLAGS += -std=c++11 -Os
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H"

else ifeq ($(CONFIG),afl-gcc)
CXX = AFL_QUIET=1 AFL_HARDEN=1 afl-gcc
LD = AFL_QUIET=1 AFL_HARDEN=1 afl-gcc
CXXFLAGS += -std=c++11 -Os
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H"

else ifeq ($(CONFIG),cygwin)
CXX = gcc
LD = gcc
CXXFLAGS += -std=gnu++11 -Os
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H"

else ifeq ($(CONFIG),emcc)
CXX = emcc
LD = emcc
CXXFLAGS := -std=c++11 $(filter-out -fPIC -ggdb,$(CXXFLAGS))
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H -DABC_MEMALIGN=8"
EMCCFLAGS := -Os -Wno-warn-absolute-paths
EMCCFLAGS += --memory-init-file 0 --embed-file share -s NO_EXIT_RUNTIME=1
EMCCFLAGS += -s EXPORTED_FUNCTIONS="['_main','_run','_prompt','_errmsg']"
EMCCFLAGS += -s TOTAL_MEMORY=128*1024*1024
# https://github.com/kripken/emscripten/blob/master/src/settings.js
CXXFLAGS += $(EMCCFLAGS)
LDFLAGS += $(EMCCFLAGS)
LDLIBS =
EXE = .js

TARGETS := $(filter-out yosys-config,$(TARGETS))
EXTRA_TARGETS += yosysjs-$(YOSYS_VER).zip

ifeq ($(ENABLE_ABC),1)
LINK_ABC := 1
DISABLE_ABC_THREADS := 1
endif

viz.js:
	wget -O viz.js.part https://github.com/mdaines/viz.js/releases/download/0.0.3/viz.js
	mv viz.js.part viz.js

yosysjs-$(YOSYS_VER).zip: yosys.js viz.js misc/yosysjs/*
	rm -rf yosysjs-$(YOSYS_VER) yosysjs-$(YOSYS_VER).zip
	mkdir -p yosysjs-$(YOSYS_VER)
	cp viz.js misc/yosysjs/* yosys.js yosysjs-$(YOSYS_VER)/
	zip -r yosysjs-$(YOSYS_VER).zip yosysjs-$(YOSYS_VER)

yosys.html: misc/yosys.html
	$(P) cp misc/yosys.html yosys.html

else ifeq ($(CONFIG),mxe)
PKG_CONFIG = /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-pkg-config
CXX = /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-g++
LD = /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-g++
CXXFLAGS += -std=c++11 -Os -D_POSIX_SOURCE -DYOSYS_MXE_HACKS -Wno-attributes
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
LDFLAGS := $(filter-out -rdynamic,$(LDFLAGS)) -s
LDLIBS := $(filter-out -lrt,$(LDLIBS))
ABCMKARGS += ARCHFLAGS="-DWIN32_NO_DLL -DHAVE_STRUCT_TIMESPEC -fpermissive -w"
# TODO: Try to solve pthread linking issue in more appropriate way
ABCMKARGS += LIBS="lib/x86/pthreadVC2.lib -s" LDFLAGS="-Wl,--allow-multiple-definition" ABC_USE_NO_READLINE=1 CC="/usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-gcc"
EXE = .exe

else ifeq ($(CONFIG),msys2)
CXX = i686-w64-mingw32-g++
LD = i686-w64-mingw32-g++
CXXFLAGS += -std=c++11 -Os -D_POSIX_SOURCE -DYOSYS_WIN32_UNIX_DIR
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
LDFLAGS := $(filter-out -rdynamic,$(LDFLAGS)) -s
LDLIBS := $(filter-out -lrt,$(LDLIBS))
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H -DWIN32_NO_DLL -DHAVE_STRUCT_TIMESPEC -fpermissive -w"
ABCMKARGS += LIBS="-lpthread -s" ABC_USE_NO_READLINE=0 CC="i686-w64-mingw32-gcc" CXX="$(CXX)"
EXE = .exe

else ifeq ($(CONFIG),msys2-64)
CXX = x86_64-w64-mingw32-g++
LD = x86_64-w64-mingw32-g++
CXXFLAGS += -std=c++11 -Os -D_POSIX_SOURCE -DYOSYS_WIN32_UNIX_DIR
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
LDFLAGS := $(filter-out -rdynamic,$(LDFLAGS)) -s
LDLIBS := $(filter-out -lrt,$(LDLIBS))
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H -DWIN32_NO_DLL -DHAVE_STRUCT_TIMESPEC -fpermissive -w"
ABCMKARGS += LIBS="-lpthread -s" ABC_USE_NO_READLINE=0 CC="x86_64-w64-mingw32-gcc" CXX="$(CXX)"
EXE = .exe

else ifneq ($(CONFIG),none)
$(error Invalid CONFIG setting '$(CONFIG)'. Valid values: clang, gcc, gcc-4.8, emcc, mxe, msys2, msys2-64)
endif

ifeq ($(ENABLE_LIBYOSYS),1)
TARGETS += libyosys.so
endif

ifeq ($(ENABLE_PYOSYS),1)

#Detect name of boost_python library. Some distros usbe boost_python-py<version>, other boost_python<version>, some only use the major version number, some a concatenation of major and minor version numbers
ifeq ($(OS), Darwin)
BOOST_PYTHON_LIB ?= $(shell \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null $(shell $(PYTHON_EXECUTABLE)-config --ldflags) -lboost_python-py$(subst .,,$(PYTHON_VERSION)) - > /dev/null 2>&1;        then echo "-lboost_python-py$(subst .,,$(PYTHON_VERSION))";       else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null $(shell $(PYTHON_EXECUTABLE)-config --ldflags) -lboost_python-py$(subst .,,$(PYTHON_MAJOR_VERSION)) - > /dev/null 2>&1;  then echo "-lboost_python-py$(subst .,,$(PYTHON_MAJOR_VERSION))"; else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null $(shell $(PYTHON_EXECUTABLE)-config --ldflags) -lboost_python$(subst .,,$(PYTHON_VERSION)) - > /dev/null 2>&1;           then echo "-lboost_python$(subst .,,$(PYTHON_VERSION))";          else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null $(shell $(PYTHON_EXECUTABLE)-config --ldflags) -lboost_python$(subst .,,$(PYTHON_MAJOR_VERSION)) - > /dev/null 2>&1;     then echo "-lboost_python$(subst .,,$(PYTHON_MAJOR_VERSION))";    else \
                                                                                                                                                                                        echo ""; fi; fi; fi; fi;)
else
BOOST_PYTHON_LIB ?= $(shell \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null `$(PYTHON_EXECUTABLE)-config --libs` -lboost_python-py$(subst .,,$(PYTHON_VERSION)) - > /dev/null 2>&1;        then echo "-lboost_python-py$(subst .,,$(PYTHON_VERSION))";       else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null `$(PYTHON_EXECUTABLE)-config --libs` -lboost_python-py$(subst .,,$(PYTHON_MAJOR_VERSION)) - > /dev/null 2>&1;  then echo "-lboost_python-py$(subst .,,$(PYTHON_MAJOR_VERSION))"; else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null `$(PYTHON_EXECUTABLE)-config --libs` -lboost_python$(subst .,,$(PYTHON_VERSION)) - > /dev/null 2>&1;           then echo "-lboost_python$(subst .,,$(PYTHON_VERSION))";          else \
	if echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null `$(PYTHON_EXECUTABLE)-config --libs` -lboost_python$(subst .,,$(PYTHON_MAJOR_VERSION)) - > /dev/null 2>&1;     then echo "-lboost_python$(subst .,,$(PYTHON_MAJOR_VERSION))";    else \
                                                                                                                                                                                        echo ""; fi; fi; fi; fi;)
endif

ifeq ($(BOOST_PYTHON_LIB),)
$(error BOOST_PYTHON_LIB could not be detected. Please define manualy)
endif

ifeq ($(OS), Darwin)
ifeq ($(PYTHON_MAJOR_VERSION),3)
LDLIBS += $(shell $(PYTHON_EXECUTABLE)-config --ldflags) $(BOOST_PYTHON_LIB) -lboost_system -lboost_filesystem
CXXFLAGS += $(shell $(PYTHON_EXECUTABLE)-config --includes) -DWITH_PYTHON
else
LDLIBS += $(shell $(PYTHON_EXECUTABLE)-config --ldflags) $(BOOST_PYTHON_LIB) -lboost_system -lboost_filesystem
CXXFLAGS += $(shell $(PYTHON_EXECUTABLE)-config --includes) -DWITH_PYTHON
endif
else
ifeq ($(PYTHON_MAJOR_VERSION),3)
LDLIBS += $(shell $(PYTHON_EXECUTABLE)-config --libs) $(BOOST_PYTHON_LIB) -lboost_system -lboost_filesystem
CXXFLAGS += $(shell $(PYTHON_EXECUTABLE)-config --includes) -DWITH_PYTHON
else
LDLIBS += $(shell $(PYTHON_EXECUTABLE)-config --libs) $(BOOST_PYTHON_LIB) -lboost_system -lboost_filesystem
CXXFLAGS += $(shell $(PYTHON_EXECUTABLE)-config --includes) -DWITH_PYTHON
endif
endif

ifeq ($(ENABLE_PYOSYS),1)
PY_WRAPPER_FILE = kernel/python_wrappers
OBJS += $(PY_WRAPPER_FILE).o
PY_GEN_SCRIPT= py_wrap_generator
PY_WRAP_INCLUDES := $(shell python$(PYTHON_VERSION) -c "from misc import $(PY_GEN_SCRIPT); $(PY_GEN_SCRIPT).print_includes()")
endif
endif

ifeq ($(ENABLE_READLINE),1)
CXXFLAGS += -DYOSYS_ENABLE_READLINE
ifeq ($(OS), FreeBSD)
CXXFLAGS += -I/usr/local/include
endif
LDLIBS += -lreadline
ifeq ($(LINK_CURSES),1)
LDLIBS += -lcurses
ABCMKARGS += "ABC_READLINE_LIBRARIES=-lcurses -lreadline"
endif
ifeq ($(LINK_TERMCAP),1)
LDLIBS += -ltermcap
ABCMKARGS += "ABC_READLINE_LIBRARIES=-lreadline -ltermcap"
endif
ifeq ($(CONFIG),mxe)
LDLIBS += -ltermcap
endif
else
ifeq ($(ENABLE_EDITLINE),1)
CXXFLAGS += -DYOSYS_ENABLE_EDITLINE
LDLIBS += -ledit -ltinfo -lbsd
else
ABCMKARGS += "ABC_USE_NO_READLINE=1"
endif
endif

ifeq ($(DISABLE_ABC_THREADS),1)
ABCMKARGS += "ABC_USE_NO_PTHREADS=1"
endif

ifeq ($(ENABLE_PLUGINS),1)
CXXFLAGS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --cflags libffi) -DYOSYS_ENABLE_PLUGINS
LDLIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs libffi || echo -lffi)
ifneq ($(OS), FreeBSD)
LDLIBS += -ldl
endif
endif

ifeq ($(ENABLE_GLOB),1)
CXXFLAGS += -DYOSYS_ENABLE_GLOB
endif

ifeq ($(ENABLE_TCL),1)
TCL_VERSION ?= tcl$(shell bash -c "tclsh <(echo 'puts [info tclversion]')")
ifeq ($(OS), FreeBSD)
TCL_INCLUDE ?= /usr/local/include/$(TCL_VERSION)
else
TCL_INCLUDE ?= /usr/include/$(TCL_VERSION)
endif

ifeq ($(CONFIG),mxe)
CXXFLAGS += -DYOSYS_ENABLE_TCL
LDLIBS += -ltcl86 -lwsock32 -lws2_32 -lnetapi32 -lz -luserenv
else
CXXFLAGS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --cflags tcl || echo -I$(TCL_INCLUDE)) -DYOSYS_ENABLE_TCL
ifeq ($(OS), FreeBSD)
# FreeBSD uses tcl8.6, but lib is named "libtcl86"
LDLIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs tcl || echo -l$(TCL_VERSION) | tr -d '.')
else
LDLIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs tcl || echo -l$(TCL_VERSION))
endif
endif
endif

ifeq ($(ENABLE_GCOV),1)
CXXFLAGS += --coverage
LDFLAGS += --coverage
endif

ifeq ($(ENABLE_GPROF),1)
CXXFLAGS += -pg
LDFLAGS += -pg
endif

ifeq ($(ENABLE_NDEBUG),1)
CXXFLAGS := -O3 -DNDEBUG $(filter-out -Os -ggdb,$(CXXFLAGS))
endif

ifeq ($(ENABLE_DEBUG),1)
ifeq ($(CONFIG),clang)
CXXFLAGS := -O0 -DDEBUG $(filter-out -Os,$(CXXFLAGS))
else
CXXFLAGS := -Og -DDEBUG $(filter-out -Os,$(CXXFLAGS))
endif
endif

ifeq ($(ENABLE_ABC),1)
CXXFLAGS += -DYOSYS_ENABLE_ABC
ifeq ($(LINK_ABC),1)
CXXFLAGS += -DYOSYS_LINK_ABC
ifeq ($(DISABLE_ABC_THREADS),0)
LDLIBS += -lpthread
endif
else
ifeq ($(ABCEXTERNAL),)
TARGETS += yosys-abc$(EXE)
endif
endif
endif

ifeq ($(ENABLE_VERIFIC),1)
VERIFIC_DIR ?= /usr/local/src/verific_lib
VERIFIC_COMPONENTS ?= verilog vhdl database util containers hier_tree
CXXFLAGS += $(patsubst %,-I$(VERIFIC_DIR)/%,$(VERIFIC_COMPONENTS)) -DYOSYS_ENABLE_VERIFIC
ifeq ($(OS), Darwin)
LDLIBS += $(patsubst %,$(VERIFIC_DIR)/%/*-mac.a,$(VERIFIC_COMPONENTS)) -lz
else
LDLIBS += $(patsubst %,$(VERIFIC_DIR)/%/*-linux.a,$(VERIFIC_COMPONENTS)) -lz
endif
endif

ifeq ($(ENABLE_PROTOBUF),1)
LDLIBS += $(shell pkg-config --cflags --libs protobuf)
endif

ifeq ($(ENABLE_COVER),1)
CXXFLAGS += -DYOSYS_ENABLE_COVER
endif

define add_share_file
EXTRA_TARGETS += $(subst //,/,$(1)/$(notdir $(2)))
$(subst //,/,$(1)/$(notdir $(2))): $(2)
	$$(P) mkdir -p $(1)
	$$(Q) cp "$(YOSYS_SRC)"/$(2) $(subst //,/,$(1)/$(notdir $(2)))
endef

define add_gen_share_file
EXTRA_TARGETS += $(subst //,/,$(1)/$(notdir $(2)))
$(subst //,/,$(1)/$(notdir $(2))): $(2)
	$$(P) mkdir -p $(1)
	$$(Q) cp $(2) $(subst //,/,$(1)/$(notdir $(2)))
endef

define add_include_file
$(eval $(call add_share_file,$(dir share/include/$(1)),$(1)))
endef

ifeq ($(PRETTY), 1)
P_STATUS = 0
P_OFFSET = 0
P_UPDATE = $(eval P_STATUS=$(shell echo $(OBJS) yosys$(EXE) | $(AWK) 'BEGIN { RS = " "; I = $(P_STATUS)+0; } $$1 == "$@" && NR > I { I = NR; } END { print I; }'))
P_SHOW = [$(shell $(AWK) "BEGIN { N=$(words $(OBJS) yosys$(EXE)); printf \"%3d\", $(P_OFFSET)+90*$(P_STATUS)/N; exit; }")%]
P = @echo "$(if $(findstring $@,$(TARGETS) $(EXTRA_TARGETS)),$(eval P_OFFSET = 10))$(call P_UPDATE)$(call P_SHOW) Building $@";
Q = @
S = -s
else
P_SHOW = ->
P =
Q =
S =
endif

$(eval $(call add_include_file,kernel/yosys.h))
$(eval $(call add_include_file,kernel/hashlib.h))
$(eval $(call add_include_file,kernel/log.h))
$(eval $(call add_include_file,kernel/rtlil.h))
$(eval $(call add_include_file,kernel/register.h))
$(eval $(call add_include_file,kernel/celltypes.h))
$(eval $(call add_include_file,kernel/celledges.h))
$(eval $(call add_include_file,kernel/consteval.h))
$(eval $(call add_include_file,kernel/sigtools.h))
$(eval $(call add_include_file,kernel/modtools.h))
$(eval $(call add_include_file,kernel/macc.h))
$(eval $(call add_include_file,kernel/utils.h))
$(eval $(call add_include_file,kernel/satgen.h))
$(eval $(call add_include_file,libs/ezsat/ezsat.h))
$(eval $(call add_include_file,libs/ezsat/ezminisat.h))
$(eval $(call add_include_file,libs/sha1/sha1.h))
$(eval $(call add_include_file,passes/fsm/fsmdata.h))
$(eval $(call add_include_file,frontends/ast/ast.h))
$(eval $(call add_include_file,backends/ilang/ilang_backend.h))

OBJS += kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o kernel/yosys.o
OBJS += kernel/cellaigs.o kernel/celledges.o

kernel/log.o: CXXFLAGS += -DYOSYS_SRC='"$(YOSYS_SRC)"'
kernel/yosys.o: CXXFLAGS += -DYOSYS_DATDIR='"$(DATDIR)"'

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

include $(YOSYS_SRC)/frontends/*/Makefile.inc
include $(YOSYS_SRC)/passes/*/Makefile.inc
include $(YOSYS_SRC)/backends/*/Makefile.inc
include $(YOSYS_SRC)/techlibs/*/Makefile.inc

else

include frontends/verilog/Makefile.inc
include frontends/ilang/Makefile.inc
include frontends/ast/Makefile.inc
include frontends/blif/Makefile.inc

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

include backends/verilog/Makefile.inc
include backends/ilang/Makefile.inc

include techlibs/common/Makefile.inc

endif

ifeq ($(LINK_ABC),1)
OBJS += yosys-libabc.a
endif

top-all: $(TARGETS) $(EXTRA_TARGETS)
	@echo ""
	@echo "  Build successful."
	@echo ""

ifeq ($(CONFIG),emcc)
yosys.js: $(filter-out yosysjs-$(YOSYS_VER).zip,$(EXTRA_TARGETS))
endif

yosys$(EXE): $(OBJS)
	$(P) $(LD) -o yosys$(EXE) $(LDFLAGS) $(OBJS) $(LDLIBS)

libyosys.so: $(filter-out kernel/driver.o,$(OBJS))
ifeq ($(OS), Darwin)
	$(P) $(LD) -o libyosys.so -shared -Wl,-install_name,libyosys.so $(LDFLAGS) $^ $(LDLIBS)
else
	$(P) $(LD) -o libyosys.so -shared -Wl,-soname,libyosys.so $(LDFLAGS) $^ $(LDLIBS)
endif

%.o: %.cc
	$(Q) mkdir -p $(dir $@)
	$(P) $(CXX) -o $@ -c $(CPPFLAGS) $(CXXFLAGS) $<

%.pyh: %.h
	$(Q) mkdir -p $(dir $@)
	$(P) cat $< | grep -E -v "#[ ]*(include|error)" | $(LD) -x c++ -o $@ -E -P -

ifeq ($(ENABLE_PYOSYS),1)
$(PY_WRAPPER_FILE).cc: misc/$(PY_GEN_SCRIPT).py $(PY_WRAP_INCLUDES)
	$(Q) mkdir -p $(dir $@)
	$(P) python$(PYTHON_VERSION) -c "from misc import $(PY_GEN_SCRIPT); $(PY_GEN_SCRIPT).gen_wrappers(\"$(PY_WRAPPER_FILE).cc\")"
endif

%.o: %.cpp
	$(Q) mkdir -p $(dir $@)
	$(P) $(CXX) -o $@ -c $(CPPFLAGS) $(CXXFLAGS) $<

YOSYS_VER_STR := Yosys $(YOSYS_VER) (git sha1 $(GIT_REV), $(notdir $(CXX)) $(shell \
		$(CXX) --version | tr ' ()' '\n' | grep '^[0-9]' | head -n1) $(filter -f% -m% -O% -DNDEBUG,$(CXXFLAGS)))

kernel/version_$(GIT_REV).cc: $(YOSYS_SRC)/Makefile
	$(P) rm -f kernel/version_*.o kernel/version_*.d kernel/version_*.cc
	$(Q) mkdir -p kernel && echo "namespace Yosys { extern const char *yosys_version_str; const char *yosys_version_str=\"$(YOSYS_VER_STR)\"; }" > kernel/version_$(GIT_REV).cc

ifeq ($(ENABLE_VERIFIC),1)
CXXFLAGS_NOVERIFIC = $(foreach v,$(CXXFLAGS),$(if $(findstring $(VERIFIC_DIR),$(v)),,$(v)))
LDLIBS_NOVERIFIC = $(foreach v,$(LDLIBS),$(if $(findstring $(VERIFIC_DIR),$(v)),,$(v)))
else
CXXFLAGS_NOVERIFIC = $(CXXFLAGS)
LDLIBS_NOVERIFIC = $(LDLIBS)
endif

yosys-config: misc/yosys-config.in
	$(P) $(SED) -e 's#@CXXFLAGS@#$(subst -I. -I"$(YOSYS_SRC)",-I"$(DATDIR)/include",$(strip $(CXXFLAGS_NOVERIFIC)))#;' \
			-e 's#@CXX@#$(strip $(CXX))#;' -e 's#@LDFLAGS@#$(strip $(LDFLAGS) $(PLUGIN_LDFLAGS))#;' -e 's#@LDLIBS@#$(strip $(LDLIBS_NOVERIFIC))#;' \
			-e 's#@BINDIR@#$(strip $(BINDIR))#;' -e 's#@DATDIR@#$(strip $(DATDIR))#;' < $< > yosys-config
	$(Q) chmod +x yosys-config

abc/abc-$(ABCREV)$(EXE) abc/libabc-$(ABCREV).a:
	$(P)
ifneq ($(ABCREV),default)
	$(Q) if test -d abc/.hg; then \
		echo 'REEBE: NOP qverpgbel vf n ut jbexvat pbcl! Erzbir nop/ naq er-eha "znxr".' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; false; \
	fi
	$(Q) if ( cd abc 2> /dev/null && ! git diff-index --quiet HEAD; ); then \
		echo 'REEBE: NOP pbagnvaf ybpny zbqvsvpngvbaf! Frg NOPERI=qrsnhyg va Lbflf Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; false; \
	fi
	$(Q) if test "`cd abc 2> /dev/null && git rev-parse --short HEAD`" != "$(ABCREV)"; then \
		test $(ABCPULL) -ne 0 || { echo 'REEBE: NOP abg hc gb qngr naq NOPCHYY frg gb 0 va Znxrsvyr!' | tr 'A-Za-z' 'N-ZA-Mn-za-m'; exit 1; }; \
		echo "Pulling ABC from $(ABCURL):"; set -x; \
		test -d abc || git clone $(ABCURL) abc; \
		cd abc && $(MAKE) DEP= clean && git fetch origin master && git checkout $(ABCREV); \
	fi
endif
	$(Q) rm -f abc/abc-[0-9a-f]*
	$(Q) cd abc && $(MAKE) $(S) $(ABCMKARGS) $(if $(filter %.a,$@),PROG="abc-$(ABCREV)",PROG="abc-$(ABCREV)$(EXE)") MSG_PREFIX="$(eval P_OFFSET = 5)$(call P_SHOW)$(eval P_OFFSET = 10) ABC: " $(if $(filter %.a,$@),libabc-$(ABCREV).a)

ifeq ($(ABCREV),default)
.PHONY: abc/abc-$(ABCREV)$(EXE)
.PHONY: abc/libabc-$(ABCREV).a
endif

yosys-abc$(EXE): abc/abc-$(ABCREV)$(EXE)
	$(P) cp abc/abc-$(ABCREV)$(EXE) yosys-abc$(EXE)

yosys-libabc.a: abc/libabc-$(ABCREV).a
	$(P) cp abc/libabc-$(ABCREV).a yosys-libabc.a

ifneq ($(SEED),)
SEEDOPT="-S $(SEED)"
else
SEEDOPT=""
endif

ifneq ($(ABCEXTERNAL),)
ABCOPT="-A $(ABCEXTERNAL)"
else
ABCOPT=""
endif

test: $(TARGETS) $(EXTRA_TARGETS)
	+cd tests/simple && bash run-test.sh $(SEEDOPT)
	+cd tests/hana && bash run-test.sh $(SEEDOPT)
	+cd tests/asicworld && bash run-test.sh $(SEEDOPT)
	# +cd tests/realmath && bash run-test.sh $(SEEDOPT)
	+cd tests/share && bash run-test.sh $(SEEDOPT)
	+cd tests/fsm && bash run-test.sh $(SEEDOPT)
	+cd tests/techmap && bash run-test.sh
	+cd tests/memories && bash run-test.sh $(ABCOPT) $(SEEDOPT)
	+cd tests/bram && bash run-test.sh $(SEEDOPT)
	+cd tests/various && bash run-test.sh
	+cd tests/sat && bash run-test.sh
	+cd tests/svinterfaces && bash run-test.sh $(SEEDOPT)
	+cd tests/opt && bash run-test.sh
	+cd tests/aiger && bash run-test.sh $(ABCOPT)
	+cd tests/arch && bash run-test.sh
	@echo ""
	@echo "  Passed \"make test\"."
	@echo ""

VALGRIND ?= valgrind --error-exitcode=1 --leak-check=full --show-reachable=yes --errors-for-leak-kinds=all

vgtest: $(TARGETS) $(EXTRA_TARGETS)
	$(VALGRIND) ./yosys -p 'setattr -mod -unset top; synth' $$( ls tests/simple/*.v | grep -v repwhile.v )
	@echo ""
	@echo "  Passed \"make vgtest\"."
	@echo ""

vloghtb: $(TARGETS) $(EXTRA_TARGETS)
	+cd tests/vloghtb && bash run-test.sh
	@echo ""
	@echo "  Passed \"make vloghtb\"."
	@echo ""

ystests: $(TARGETS) $(EXTRA_TARGETS)
	rm -rf tests/ystests
	git clone -b yosys-0.9-rc https://github.com/YosysHQ/yosys-tests.git tests/ystests
	+$(MAKE) PATH="$$PWD:$$PATH" -C tests/ystests
	@echo ""
	@echo "  Finished \"make ystests\"."
	@echo ""

# Unit test
unit-test: libyosys.so
	@$(MAKE) -C $(UNITESTPATH) CXX="$(CXX)" CPPFLAGS="$(CPPFLAGS)" \
		CXXFLAGS="$(CXXFLAGS)" LDLIBS="$(LDLIBS)" ROOTPATH="$(CURDIR)"

clean-unit-test:
	@$(MAKE) -C $(UNITESTPATH) clean

install: $(TARGETS) $(EXTRA_TARGETS)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(BINDIR)
	$(INSTALL_SUDO) cp $(TARGETS) $(DESTDIR)$(BINDIR)
ifneq ($(filter yosys,$(TARGETS)),)
	$(INSTALL_SUDO) $(STRIP) -S $(DESTDIR)$(BINDIR)/yosys
endif
ifneq ($(filter yosys-abc,$(TARGETS)),)
	$(INSTALL_SUDO) $(STRIP) $(DESTDIR)$(BINDIR)/yosys-abc
endif
ifneq ($(filter yosys-filterlib,$(TARGETS)),)
	$(INSTALL_SUDO) $(STRIP) $(DESTDIR)$(BINDIR)/yosys-filterlib
endif
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(DATDIR)
	$(INSTALL_SUDO) cp -r share/. $(DESTDIR)$(DATDIR)/.
ifeq ($(ENABLE_LIBYOSYS),1)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(LIBDIR)
	$(INSTALL_SUDO) cp libyosys.so $(DESTDIR)$(LIBDIR)/
	$(INSTALL_SUDO) $(STRIP) -S $(DESTDIR)$(LIBDIR)/libyosys.so
ifeq ($(ENABLE_PYOSYS),1)
	$(INSTALL_SUDO) mkdir -p $(PYTHON_DESTDIR)/pyosys
	$(INSTALL_SUDO) cp libyosys.so $(PYTHON_DESTDIR)/pyosys/
	$(INSTALL_SUDO) cp misc/__init__.py $(PYTHON_DESTDIR)/pyosys/
endif
endif

uninstall:
	$(INSTALL_SUDO) rm -vf $(addprefix $(DESTDIR)$(BINDIR)/,$(notdir $(TARGETS)))
	$(INSTALL_SUDO) rm -rvf $(DESTDIR)$(DATDIR)
ifeq ($(ENABLE_LIBYOSYS),1)
	$(INSTALL_SUDO) rm -vf $(DESTDIR)$(LIBDIR)/libyosys.so
ifeq ($(ENABLE_PYOSYS),1)
	$(INSTALL_SUDO) rm -vf $(PYTHON_DESTDIR)/pyosys/libyosys.so
	$(INSTALL_SUDO) rm -vf $(PYTHON_DESTDIR)/pyosys/__init__.py
	$(INSTALL_SUDO) rmdir $(PYTHON_DESTDIR)/pyosys
endif
endif

update-manual: $(TARGETS) $(EXTRA_TARGETS)
	cd manual && ../yosys -p 'help -write-tex-command-reference-manual'

manual: $(TARGETS) $(EXTRA_TARGETS)
	cd manual && bash appnotes.sh
	cd manual && bash presentation.sh
	cd manual && bash manual.sh

clean:
	rm -rf share
	rm -rf kernel/*.pyh
	if test -d manual; then cd manual && sh clean.sh; fi
	rm -f $(OBJS) $(GENFILES) $(TARGETS) $(EXTRA_TARGETS) $(EXTRA_OBJS) $(PY_WRAP_INCLUDES) $(PY_WRAPPER_FILE).cc
	rm -f kernel/version_*.o kernel/version_*.cc abc/abc-[0-9a-f]* abc/libabc-[0-9a-f]*.a
	rm -f libs/*/*.d frontends/*/*.d passes/*/*.d backends/*/*.d kernel/*.d techlibs/*/*.d
	rm -rf tests/asicworld/*.out tests/asicworld/*.log
	rm -rf tests/hana/*.out tests/hana/*.log
	rm -rf tests/simple/*.out tests/simple/*.log
	rm -rf tests/memories/*.out tests/memories/*.log tests/memories/*.dmp
	rm -rf tests/sat/*.log tests/techmap/*.log tests/various/*.log
	rm -rf tests/bram/temp tests/fsm/temp tests/realmath/temp tests/share/temp tests/smv/temp
	rm -rf vloghtb/Makefile vloghtb/refdat vloghtb/rtl vloghtb/scripts vloghtb/spec vloghtb/check_yosys vloghtb/vloghammer_tb.tar.bz2 vloghtb/temp vloghtb/log_test_*
	rm -f tests/svinterfaces/*.log_stdout tests/svinterfaces/*.log_stderr tests/svinterfaces/dut_result.txt tests/svinterfaces/reference_result.txt tests/svinterfaces/a.out tests/svinterfaces/*_syn.v tests/svinterfaces/*.diff
	rm -f  tests/tools/cmp_tbdata

clean-abc:
	$(MAKE) -C abc DEP= clean
	rm -f yosys-abc$(EXE) yosys-libabc.a abc/abc-[0-9a-f]* abc/libabc-[0-9a-f]*.a

mrproper: clean
	git clean -xdf

coverage:
	./yosys -qp 'help; help -all'
	rm -rf coverage.info coverage_html
	lcov --capture -d . --no-external -o coverage.info
	genhtml coverage.info --output-directory coverage_html

qtcreator:
	{ for file in $(basename $(OBJS)); do \
		for prefix in cc y l; do if [ -f $${file}.$${prefix} ]; then echo $$file.$${prefix}; fi; done \
	done; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \); } > qtcreator.files
	{ echo .; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \) -printf '%h\n' | sort -u; } > qtcreator.includes
	touch qtcreator.config qtcreator.creator

vcxsrc: $(GENFILES) $(EXTRA_TARGETS)
	rm -rf yosys-win32-vcxsrc-$(YOSYS_VER){,.zip}
	set -e; for f in `ls $(filter %.cc %.cpp,$(GENFILES)) $(addsuffix .cc,$(basename $(OBJS))) $(addsuffix .cpp,$(basename $(OBJS))) 2> /dev/null`; do \
		echo "Analyse: $$f" >&2; cpp -std=c++11 -MM -I. -D_YOSYS_ $$f; done | sed 's,.*:,,; s,//*,/,g; s,/[^/]*/\.\./,/,g; y, \\,\n\n,;' | grep '^[^/]' | sort -u | grep -v kernel/version_ > srcfiles.txt
	bash misc/create_vcxsrc.sh yosys-win32-vcxsrc $(YOSYS_VER) $(GIT_REV)
	echo "namespace Yosys { extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys (Version Information Unavailable)\"; }" > kernel/version.cc
	zip yosys-win32-vcxsrc-$(YOSYS_VER)/genfiles.zip $(GENFILES) kernel/version.cc
	zip -r yosys-win32-vcxsrc-$(YOSYS_VER).zip yosys-win32-vcxsrc-$(YOSYS_VER)/
	rm -f srcfiles.txt kernel/version.cc

ifeq ($(CONFIG),mxe)
mxebin: $(TARGETS) $(EXTRA_TARGETS)
	rm -rf yosys-win32-mxebin-$(YOSYS_VER){,.zip}
	mkdir -p yosys-win32-mxebin-$(YOSYS_VER)
	cp -r yosys.exe share/ yosys-win32-mxebin-$(YOSYS_VER)/
ifeq ($(ENABLE_ABC),1)
	cp -r yosys-abc.exe abc/lib/x86/pthreadVC2.dll yosys-win32-mxebin-$(YOSYS_VER)/
endif
	echo -en 'This is Yosys $(YOSYS_VER) for Win32.\r\n' > yosys-win32-mxebin-$(YOSYS_VER)/readme.txt
	echo -en 'Documentation at http://www.clifford.at/yosys/.\r\n' >> yosys-win32-mxebin-$(YOSYS_VER)/readme.txt
	zip -r yosys-win32-mxebin-$(YOSYS_VER).zip yosys-win32-mxebin-$(YOSYS_VER)/
endif

config-clean: clean
	rm -f Makefile.conf

config-clang: clean
	echo 'CONFIG := clang' > Makefile.conf

config-gcc: clean
	echo 'CONFIG := gcc' > Makefile.conf

config-gcc-static: clean
	echo 'CONFIG := gcc-static' > Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf
	echo 'ENABLE_READLINE := 0' >> Makefile.conf
	echo 'ENABLE_TCL := 0' >> Makefile.conf

config-gcc-4.8: clean
	echo 'CONFIG := gcc-4.8' > Makefile.conf

config-afl-gcc: clean
	echo 'CONFIG := afl-gcc' > Makefile.conf

config-emcc: clean
	echo 'CONFIG := emcc' > Makefile.conf
	echo 'ENABLE_TCL := 0' >> Makefile.conf
	echo 'ENABLE_ABC := 0' >> Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf
	echo 'ENABLE_READLINE := 0' >> Makefile.conf

config-mxe: clean
	echo 'CONFIG := mxe' > Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf

config-msys2: clean
	echo 'CONFIG := msys2' > Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf

config-msys2-64: clean
	echo 'CONFIG := msys2-64' > Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf

config-cygwin: clean
	echo 'CONFIG := cygwin' > Makefile.conf

config-gcov: clean
	echo 'CONFIG := gcc' > Makefile.conf
	echo 'ENABLE_GCOV := 1' >> Makefile.conf
	echo 'ENABLE_DEBUG := 1' >> Makefile.conf

config-gprof: clean
	echo 'CONFIG := gcc' > Makefile.conf
	echo 'ENABLE_GPROF := 1' >> Makefile.conf

config-sudo:
	echo "INSTALL_SUDO := sudo" >> Makefile.conf

echo-yosys-ver:
	@echo "$(YOSYS_VER)"

echo-git-rev:
	@echo "$(GIT_REV)"

-include libs/*/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d
-include techlibs/*/*.d

.PHONY: all top-all abc test install install-abc manual clean mrproper qtcreator coverage vcxsrc mxebin
.PHONY: config-clean config-clang config-gcc config-gcc-static config-gcc-4.8 config-afl-gcc config-gprof config-sudo

