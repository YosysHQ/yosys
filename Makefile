
CONFIG := none
# CONFIG := clang
# CONFIG := gcc
# CONFIG := wasi
# CONFIG := msys2-32
# CONFIG := msys2-64

# features (the more the better)
ENABLE_TCL := 1
ENABLE_ABC := 1
ENABLE_GLOB := 1
ENABLE_PLUGINS := 1
ENABLE_READLINE := 1
ENABLE_EDITLINE := 0
ENABLE_GHDL := 0
ENABLE_VERIFIC := 0
ENABLE_VERIFIC_SYSTEMVERILOG := 1
ENABLE_VERIFIC_VHDL := 1
ENABLE_VERIFIC_HIER_TREE := 1
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS := 0
ENABLE_VERIFIC_EDIF := 0
ENABLE_VERIFIC_LIBERTY := 0
ENABLE_COVER := 1
ENABLE_LIBYOSYS := 0
ENABLE_ZLIB := 1

# python wrappers
ENABLE_PYOSYS := 0

# other configuration flags
ENABLE_GCOV := 0
ENABLE_GPROF := 0
ENABLE_DEBUG := 0
ENABLE_LTO := 0
ENABLE_CCACHE := 0
# sccache is not always a drop-in replacement for ccache in practice
ENABLE_SCCACHE := 0
ENABLE_FUNCTIONAL_TESTS := 0
LINK_CURSES := 0
LINK_TERMCAP := 0
LINK_ABC := 0
# Needed for environments that can't run executables (i.e. emscripten, wasm)
DISABLE_SPAWN := 0
# Needed for environments that don't have proper thread support (i.e. emscripten, wasm--for now)
DISABLE_ABC_THREADS := 0

# clang sanitizers
SANITIZER =
# SANITIZER = address
# SANITIZER = memory
# SANITIZER = undefined
# SANITIZER = cfi

# Prefer using ENABLE_DEBUG over setting these
OPT_LEVEL := -O3
GCC_LTO :=
CLANG_LTO := -flto=thin

PROGRAM_PREFIX :=

OS := $(shell uname -s)
PREFIX ?= /usr/local
INSTALL_SUDO :=
ifneq ($(filter MINGW%,$(OS)),)
OS := MINGW
endif

ifneq ($(wildcard Makefile.conf),)
include Makefile.conf
endif

ifeq ($(ENABLE_PYOSYS),1)
ENABLE_LIBYOSYS := 1
endif

BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/$(PROGRAM_PREFIX)yosys
DATDIR := $(PREFIX)/share/$(PROGRAM_PREFIX)yosys

EXE =
OBJS =
GENFILES =
EXTRA_OBJS =
EXTRA_TARGETS =
TARGETS = $(PROGRAM_PREFIX)yosys$(EXE) $(PROGRAM_PREFIX)yosys-config

PRETTY = 1
SMALL = 0

# Unit test
UNITESTPATH := tests/unit

all: top-all

YOSYS_SRC := $(dir $(firstword $(MAKEFILE_LIST)))
VPATH := $(YOSYS_SRC)

CXXSTD ?= c++17
CXXFLAGS := $(CXXFLAGS) -Wall -Wextra -ggdb -I. -I"$(YOSYS_SRC)" -MD -MP -D_YOSYS_ -fPIC -I$(PREFIX)/include
LIBS := $(LIBS) -lstdc++ -lm
PLUGIN_LINKFLAGS :=
PLUGIN_LIBS :=
EXE_LINKFLAGS :=
EXE_LIBS :=
ifeq ($(OS), MINGW)
EXE_LINKFLAGS := -Wl,--export-all-symbols -Wl,--out-implib,libyosys_exe.a
PLUGIN_LINKFLAGS += -L"$(LIBDIR)"
PLUGIN_LIBS := -lyosys_exe
endif

PKG_CONFIG ?= pkg-config
SED ?= sed
BISON ?= bison
STRIP ?= strip
AWK ?= awk

ifneq ($(shell :; command -v rsync),)
RSYNC_CP ?= rsync -rc
else
RSYNC_CP ?= cp -ru
endif

ifeq ($(OS), Darwin)
PLUGIN_LINKFLAGS += -undefined dynamic_lookup
LINKFLAGS += -rdynamic

# homebrew search paths
ifneq ($(shell :; command -v brew),)
BREW_PREFIX := $(shell brew --prefix)/opt
$(info $$BREW_PREFIX is [${BREW_PREFIX}])
ifeq ($(ENABLE_PYOSYS),1)
CXXFLAGS += -I$(BREW_PREFIX)/boost/include
LINKFLAGS += -L$(BREW_PREFIX)/boost/lib -L$(BREW_PREFIX)/boost-python3/lib
endif
CXXFLAGS += -I$(BREW_PREFIX)/readline/include
LINKFLAGS += -L$(BREW_PREFIX)/readline/lib
PKG_CONFIG_PATH := $(BREW_PREFIX)/libffi/lib/pkgconfig:$(PKG_CONFIG_PATH)
PKG_CONFIG_PATH := $(BREW_PREFIX)/tcl-tk/lib/pkgconfig:$(PKG_CONFIG_PATH)
export PATH := $(BREW_PREFIX)/bison/bin:$(BREW_PREFIX)/gettext/bin:$(BREW_PREFIX)/flex/bin:$(PATH)

# macports search paths
else ifneq ($(shell :; command -v port),)
PORT_PREFIX := $(patsubst %/bin/port,%,$(shell :; command -v port))
CXXFLAGS += -I$(PORT_PREFIX)/include
LINKFLAGS += -L$(PORT_PREFIX)/lib
PKG_CONFIG_PATH := $(PORT_PREFIX)/lib/pkgconfig:$(PKG_CONFIG_PATH)
export PATH := $(PORT_PREFIX)/bin:$(PATH)
endif

else
LINKFLAGS += -rdynamic
ifneq ($(OS), OpenBSD)
LIBS += -lrt
endif
endif

ifeq ($(OS), Haiku)
# Allow usage of non-posix vasprintf, mkstemps functions
CXXFLAGS += -D_DEFAULT_SOURCE
endif

YOSYS_VER := 0.54+1
YOSYS_MAJOR := $(shell echo $(YOSYS_VER) | cut -d'.' -f1)
YOSYS_MINOR := $(shell echo $(YOSYS_VER) | cut -d'.' -f2 | cut -d'+' -f1)
YOSYS_COMMIT := $(shell echo $(YOSYS_VER) | cut -d'+' -f2)
CXXFLAGS += -DYOSYS_VER=\\"$(YOSYS_VER)\\" \
			-DYOSYS_MAJOR=$(YOSYS_MAJOR) \
			-DYOSYS_MINOR=$(YOSYS_MINOR) \
			-DYOSYS_COMMIT=$(YOSYS_COMMIT)

# Note: We arrange for .gitcommit to contain the (short) commit hash in
# tarballs generated with git-archive(1) using .gitattributes. The git repo
# will have this file in its unexpanded form tough, in which case we fall
# back to calling git directly.
TARBALL_GIT_REV := $(shell cat $(YOSYS_SRC)/.gitcommit)
ifneq ($(findstring Format:,$(TARBALL_GIT_REV)),)
GIT_REV := $(shell GIT_DIR=$(YOSYS_SRC)/.git git rev-parse --short=9 HEAD || echo UNKNOWN)
else
GIT_REV := $(TARBALL_GIT_REV)
endif

OBJS = kernel/version_$(GIT_REV).o

bumpversion:
	sed -i "/^YOSYS_VER := / s/+[0-9][0-9]*$$/+`git log --oneline db72ec3.. | wc -l`/;" Makefile

ABCMKARGS = CC="$(CXX)" CXX="$(CXX)" ABC_USE_LIBSTDCXX=1 ABC_USE_NAMESPACE=abc VERBOSE=$(Q)

# set ABCEXTERNAL = <abc-command> to use an external ABC instance
# Note: The in-tree ABC (yosys-abc) will not be installed when ABCEXTERNAL is set.
ABCEXTERNAL ?=

define newline


endef

ifneq ($(wildcard Makefile.conf),)
# don't echo Makefile.conf contents when invoked to print source versions
ifeq ($(findstring echo-,$(MAKECMDGOALS)),)
$(info $(subst $$--$$,$(newline),$(shell sed 's,^,[Makefile.conf] ,; s,$$,$$--$$,;' < Makefile.conf | tr -d '\n' | sed 's,\$$--\$$$$,,')))
endif
include Makefile.conf
endif

PYTHON_EXECUTABLE ?= $(shell if python3 -c ""; then echo "python3"; else echo "python"; fi)
ifeq ($(ENABLE_PYOSYS),1)
PYTHON_VERSION_TESTCODE := "import sys;t='{v[0]}.{v[1]}'.format(v=list(sys.version_info[:2]));print(t)"
PYTHON_VERSION := $(shell $(PYTHON_EXECUTABLE) -c ""$(PYTHON_VERSION_TESTCODE)"")
PYTHON_MAJOR_VERSION := $(shell echo $(PYTHON_VERSION) | cut -f1 -d.)

PYTHON_CONFIG := $(PYTHON_EXECUTABLE)-config
PYTHON_CONFIG_FOR_EXE := $(PYTHON_CONFIG)
PYTHON_CONFIG_EMBED_AVAILABLE ?= $(shell $(PYTHON_EXECUTABLE)-config --embed --libs > /dev/null && echo 1)
ifeq ($(PYTHON_CONFIG_EMBED_AVAILABLE),1)
PYTHON_CONFIG_FOR_EXE := $(PYTHON_CONFIG) --embed
endif

PYTHON_DESTDIR := $(shell $(PYTHON_EXECUTABLE) -c "import site; print(site.getsitepackages()[-1]);")

# Reload Makefile.conf to override python specific variables if defined
ifneq ($(wildcard Makefile.conf),)
include Makefile.conf
endif

endif

ABC_ARCHFLAGS = ""
ifeq ($(OS), OpenBSD)
ABC_ARCHFLAGS += "-DABC_NO_RLIMIT"
endif

# This gets overridden later.
LTOFLAGS := $(GCC_LTO)

ifeq ($(CONFIG),clang)
CXX = clang++
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL)
ifeq ($(ENABLE_LTO),1)
LINKFLAGS += -fuse-ld=lld
endif
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H $(ABC_ARCHFLAGS)"
LTOFLAGS := $(CLANG_LTO)

ifneq ($(SANITIZER),)
$(info [Clang Sanitizer] $(SANITIZER))
CXXFLAGS += -g -O1 -fno-omit-frame-pointer -fno-optimize-sibling-calls -fsanitize=$(SANITIZER)
LINKFLAGS += -g -fsanitize=$(SANITIZER)
ifneq ($(findstring address,$(SANITIZER)),)
ENABLE_COVER := 0
endif
ifneq ($(findstring memory,$(SANITIZER)),)
CXXFLAGS += -fPIE -fsanitize-memory-track-origins
LINKFLAGS += -fPIE -fsanitize-memory-track-origins
endif
ifneq ($(findstring cfi,$(SANITIZER)),)
CXXFLAGS += -flto
LINKFLAGS += -flto
LTOFLAGS =
endif
endif

else ifeq ($(CONFIG),gcc)
CXX = g++
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL)
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H $(ABC_ARCHFLAGS)"

else ifeq ($(CONFIG),gcc-static)
LINKFLAGS := $(filter-out -rdynamic,$(LINKFLAGS)) -static
LIBS := $(filter-out -lrt,$(LIBS))
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL)
ABCMKARGS = CC="$(CC)" CXX="$(CXX)" LD="$(CXX)" ABC_USE_LIBSTDCXX=1 LIBS="-lm -lpthread -static" OPTFLAGS="-O" \
                       ARCHFLAGS="-DABC_USE_STDINT_H -DABC_NO_DYNAMIC_LINKING=1 -Wno-unused-but-set-variable $(ARCHFLAGS)" ABC_USE_NO_READLINE=1
ifeq ($(DISABLE_ABC_THREADS),1)
ABCMKARGS += "ABC_USE_NO_PTHREADS=1"
endif

else ifeq ($(CONFIG),wasi)
ifeq ($(WASI_SDK),)
CXX = clang++
AR = llvm-ar
RANLIB = llvm-ranlib
WASIFLAGS := -target wasm32-wasi --sysroot $(WASI_SYSROOT) $(WASIFLAGS)
else
CXX = $(WASI_SDK)/bin/clang++
AR = $(WASI_SDK)/bin/ar
RANLIB = $(WASI_SDK)/bin/ranlib
WASIFLAGS := --sysroot $(WASI_SDK)/share/wasi-sysroot $(WASIFLAGS)
endif
CXXFLAGS := $(WASIFLAGS) -std=$(CXXSTD) $(OPT_LEVEL) -D_WASI_EMULATED_PROCESS_CLOCKS $(filter-out -fPIC,$(CXXFLAGS))
LINKFLAGS := $(WASIFLAGS) -Wl,-z,stack-size=1048576 $(filter-out -rdynamic,$(LINKFLAGS))
LIBS := -lwasi-emulated-process-clocks $(filter-out -lrt,$(LIBS))
ABCMKARGS += AR="$(AR)" RANLIB="$(RANLIB)"
ABCMKARGS += ARCHFLAGS="$(WASIFLAGS) -D_WASI_EMULATED_PROCESS_CLOCKS -DABC_USE_STDINT_H -DABC_NO_DYNAMIC_LINKING -DABC_NO_RLIMIT"
ABCMKARGS += OPTFLAGS="-Os"
EXE = .wasm

DISABLE_SPAWN := 1

ifeq ($(ENABLE_ABC),1)
LINK_ABC := 1
DISABLE_ABC_THREADS := 1
endif

else ifeq ($(CONFIG),msys2-32)
CXX = i686-w64-mingw32-g++
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL) -D_POSIX_SOURCE -DYOSYS_WIN32_UNIX_DIR
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
LINKFLAGS := $(filter-out -rdynamic,$(LINKFLAGS)) -s
LIBS := $(filter-out -lrt,$(LIBS))
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H -DWIN32_NO_DLL -DWIN32 -DHAVE_STRUCT_TIMESPEC -fpermissive -w"
ABCMKARGS += LIBS="-lpthread -lshlwapi -s" ABC_USE_NO_READLINE=0 CC="i686-w64-mingw32-gcc" CXX="$(CXX)"
EXE = .exe

else ifeq ($(CONFIG),msys2-64)
CXX = x86_64-w64-mingw32-g++
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL) -D_POSIX_SOURCE -DYOSYS_WIN32_UNIX_DIR
CXXFLAGS := $(filter-out -fPIC,$(CXXFLAGS))
LINKFLAGS := $(filter-out -rdynamic,$(LINKFLAGS)) -s
LIBS := $(filter-out -lrt,$(LIBS))
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H -DWIN32_NO_DLL -DWIN32 -DHAVE_STRUCT_TIMESPEC -fpermissive -w"
ABCMKARGS += LIBS="-lpthread -lshlwapi -s" ABC_USE_NO_READLINE=0 CC="x86_64-w64-mingw32-gcc" CXX="$(CXX)"
EXE = .exe

else ifeq ($(CONFIG),none)
CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL)
ABCMKARGS += ARCHFLAGS="-DABC_USE_STDINT_H $(ABC_ARCHFLAGS)"
LTOFLAGS =

else
$(error Invalid CONFIG setting '$(CONFIG)'. Valid values: clang, gcc, msys2-32, msys2-64, none)
endif


ifeq ($(ENABLE_LTO),1)
CXXFLAGS += $(LTOFLAGS)
LINKFLAGS += $(LTOFLAGS)
endif

ifeq ($(ENABLE_LIBYOSYS),1)
TARGETS += libyosys.so
endif

ifeq ($(ENABLE_PYOSYS),1)
# python-config --ldflags includes -l and -L, but LINKFLAGS is only -L
LINKFLAGS += $(filter-out -l%,$(shell $(PYTHON_CONFIG) --ldflags))
LIBS += $(shell $(PYTHON_CONFIG) --libs)
EXE_LIBS += $(filter-out $(LIBS),$(shell $(PYTHON_CONFIG_FOR_EXE) --libs))
CXXFLAGS += $(shell $(PYTHON_CONFIG) --includes) -DWITH_PYTHON

# Detect name of boost_python library. Some distros use boost_python-py<version>, other boost_python<version>, some only use the major version number, some a concatenation of major and minor version numbers
CHECK_BOOST_PYTHON = (echo "int main(int argc, char ** argv) {return 0;}" | $(CXX) -xc -o /dev/null $(LINKFLAGS) $(EXE_LIBS) $(LIBS) -l$(1) - > /dev/null 2>&1 && echo "-l$(1)")
BOOST_PYTHON_LIB ?= $(shell \
	$(call CHECK_BOOST_PYTHON,boost_python-py$(subst .,,$(PYTHON_VERSION))) || \
	$(call CHECK_BOOST_PYTHON,boost_python-py$(PYTHON_MAJOR_VERSION)) || \
	$(call CHECK_BOOST_PYTHON,boost_python$(subst .,,$(PYTHON_VERSION))) || \
	$(call CHECK_BOOST_PYTHON,boost_python$(PYTHON_MAJOR_VERSION)) \
)

ifeq ($(BOOST_PYTHON_LIB),)
$(error BOOST_PYTHON_LIB could not be detected. Please define manually)
endif

LIBS += $(BOOST_PYTHON_LIB) -lboost_system -lboost_filesystem
PY_WRAPPER_FILE = kernel/python_wrappers
OBJS += $(PY_WRAPPER_FILE).o
PY_GEN_SCRIPT= py_wrap_generator
PY_WRAP_INCLUDES := $(shell $(PYTHON_EXECUTABLE) -c "from misc import $(PY_GEN_SCRIPT); $(PY_GEN_SCRIPT).print_includes()")
endif # ENABLE_PYOSYS

ifeq ($(ENABLE_READLINE),1)
CXXFLAGS += -DYOSYS_ENABLE_READLINE
ifeq ($(OS), $(filter $(OS),FreeBSD OpenBSD NetBSD))
CXXFLAGS += -I/usr/local/include
endif
LIBS += -lreadline
ifeq ($(LINK_CURSES),1)
LIBS += -lcurses
ABCMKARGS += "ABC_READLINE_LIBRARIES=-lcurses -lreadline"
endif
ifeq ($(LINK_TERMCAP),1)
LIBS += -ltermcap
ABCMKARGS += "ABC_READLINE_LIBRARIES=-lreadline -ltermcap"
endif
else
ifeq ($(ENABLE_EDITLINE),1)
CXXFLAGS += -DYOSYS_ENABLE_EDITLINE
LIBS += -ledit
endif
ABCMKARGS += "ABC_USE_NO_READLINE=1"
endif

ifeq ($(DISABLE_ABC_THREADS),1)
ABCMKARGS += "ABC_USE_NO_PTHREADS=1"
endif

ifeq ($(LINK_ABC),1)
ABCMKARGS += "ABC_USE_PIC=1"
endif

ifeq ($(DISABLE_SPAWN),1)
CXXFLAGS += -DYOSYS_DISABLE_SPAWN
endif

ifeq ($(ENABLE_PLUGINS),1)
CXXFLAGS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --cflags libffi) -DYOSYS_ENABLE_PLUGINS
ifeq ($(OS), MINGW)
CXXFLAGS += -Ilibs/dlfcn-win32
endif
LIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs libffi || echo -lffi)
ifneq ($(OS), $(filter $(OS),FreeBSD OpenBSD NetBSD MINGW))
LIBS += -ldl
endif
endif

ifeq ($(ENABLE_GLOB),1)
CXXFLAGS += -DYOSYS_ENABLE_GLOB
endif

ifeq ($(ENABLE_ZLIB),1)
CXXFLAGS += -DYOSYS_ENABLE_ZLIB
LIBS += -lz
endif


ifeq ($(ENABLE_TCL),1)
TCL_VERSION ?= tcl$(shell bash -c "tclsh <(echo 'puts [info tclversion]')")
ifeq ($(OS), $(filter $(OS),FreeBSD OpenBSD NetBSD))
# BSDs usually use tcl8.6, but the lib is named "libtcl86"
TCL_INCLUDE ?= /usr/local/include/$(TCL_VERSION)
TCL_LIBS ?= -l$(subst .,,$(TCL_VERSION))
else
TCL_INCLUDE ?= /usr/include/$(TCL_VERSION)
TCL_LIBS ?= -l$(TCL_VERSION)
endif

CXXFLAGS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --cflags tcl || echo -I$(TCL_INCLUDE)) -DYOSYS_ENABLE_TCL
LIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs tcl || echo $(TCL_LIBS))
ifneq (,$(findstring TCL_WITH_EXTERNAL_TOMMATH,$(CXXFLAGS)))
LIBS += $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --silence-errors --libs libtommath || echo)
endif
endif

ifeq ($(ENABLE_GCOV),1)
CXXFLAGS += --coverage
LINKFLAGS += --coverage
endif

ifeq ($(ENABLE_GPROF),1)
CXXFLAGS += -pg
LINKFLAGS += -pg
endif

ifeq ($(ENABLE_DEBUG),1)
CXXFLAGS := -Og -DDEBUG $(filter-out $(OPT_LEVEL),$(CXXFLAGS))
STRIP :=
endif

ifeq ($(ENABLE_ABC),1)
CXXFLAGS += -DYOSYS_ENABLE_ABC
ifeq ($(LINK_ABC),1)
CXXFLAGS += -DYOSYS_LINK_ABC
ifeq ($(DISABLE_ABC_THREADS),0)
LIBS += -lpthread
endif
else
ifeq ($(ABCEXTERNAL),)
TARGETS := $(PROGRAM_PREFIX)yosys-abc$(EXE) $(TARGETS)
endif
endif
endif

ifeq ($(ENABLE_GHDL),1)
GHDL_PREFIX ?= $(PREFIX)
GHDL_INCLUDE_DIR ?= $(GHDL_PREFIX)/include
GHDL_LIB_DIR ?= $(GHDL_PREFIX)/lib
CXXFLAGS += -I$(GHDL_INCLUDE_DIR) -DYOSYS_ENABLE_GHDL
LIBS += $(GHDL_LIB_DIR)/libghdl.a $(file <$(GHDL_LIB_DIR)/libghdl.link)
endif

LIBS_VERIFIC =
ifeq ($(ENABLE_VERIFIC),1)
VERIFIC_DIR ?= /usr/local/src/verific_lib
VERIFIC_COMPONENTS ?= database util containers
ifeq ($(ENABLE_VERIFIC_HIER_TREE),1)
VERIFIC_COMPONENTS += hier_tree
CXXFLAGS += -DVERIFIC_HIER_TREE_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/hier_tree),)
VERIFIC_COMPONENTS += hier_tree
endif
endif
ifeq ($(ENABLE_VERIFIC_SYSTEMVERILOG),1)
VERIFIC_COMPONENTS += verilog
CXXFLAGS += -DVERIFIC_SYSTEMVERILOG_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/verilog),)
VERIFIC_COMPONENTS += verilog
endif
endif
ifeq ($(ENABLE_VERIFIC_VHDL),1)
VERIFIC_COMPONENTS += vhdl
CXXFLAGS += -DVERIFIC_VHDL_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/vhdl),)
VERIFIC_COMPONENTS += vhdl
endif
endif
ifeq ($(ENABLE_VERIFIC_EDIF),1)
VERIFIC_COMPONENTS += edif
CXXFLAGS += -DVERIFIC_EDIF_SUPPORT
endif
ifeq ($(ENABLE_VERIFIC_LIBERTY),1)
VERIFIC_COMPONENTS += synlib
CXXFLAGS += -DVERIFIC_LIBERTY_SUPPORT
endif
ifeq ($(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS),1)
VERIFIC_COMPONENTS += extensions
CXXFLAGS += -DYOSYSHQ_VERIFIC_EXTENSIONS
else
ifneq ($(wildcard $(VERIFIC_DIR)/extensions),)
VERIFIC_COMPONENTS += extensions
endif
endif
CXXFLAGS += $(patsubst %,-I$(VERIFIC_DIR)/%,$(VERIFIC_COMPONENTS)) -DYOSYS_ENABLE_VERIFIC
ifeq ($(OS), Darwin)
LIBS_VERIFIC += $(foreach comp,$(patsubst %,$(VERIFIC_DIR)/%/*-mac.a,$(VERIFIC_COMPONENTS)),-Wl,-force_load $(comp)) -lz
else
LIBS_VERIFIC += -Wl,--whole-archive $(patsubst %,$(VERIFIC_DIR)/%/*-linux.a,$(VERIFIC_COMPONENTS)) -Wl,--no-whole-archive -lz
endif
endif


ifeq ($(ENABLE_COVER),1)
CXXFLAGS += -DYOSYS_ENABLE_COVER
endif

ifeq ($(ENABLE_CCACHE),1)
CXX := ccache $(CXX)
else
ifeq ($(ENABLE_SCCACHE),1)
CXX := sccache $(CXX)
endif
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

define add_extra_objs
EXTRA_OBJS += $(1)
.SECONDARY: $(1)
endef

ifeq ($(PRETTY), 1)
P_STATUS = 0
P_OFFSET = 0
P_UPDATE = $(eval P_STATUS=$(shell echo $(OBJS) $(PROGRAM_PREFIX)yosys$(EXE) | $(AWK) 'BEGIN { RS = " "; I = $(P_STATUS)+0; } $$1 == "$@" && NR > I { I = NR; } END { print I; }'))
P_SHOW = [$(shell $(AWK) "BEGIN { N=$(words $(OBJS) $(PROGRAM_PREFIX)yosys$(EXE)); printf \"%3d\", $(P_OFFSET)+90*$(P_STATUS)/N; exit; }")%]
P = @echo "$(if $(findstring $@,$(TARGETS) $(EXTRA_TARGETS)),$(eval P_OFFSET = 10))$(call P_UPDATE)$(call P_SHOW) Building $@";
Q = @
S = -s
else
P_SHOW = ->
P =
Q =
S =
endif

$(eval $(call add_include_file,kernel/binding.h))
$(eval $(call add_include_file,kernel/bitpattern.h))
$(eval $(call add_include_file,kernel/cellaigs.h))
$(eval $(call add_include_file,kernel/celledges.h))
$(eval $(call add_include_file,kernel/celltypes.h))
$(eval $(call add_include_file,kernel/consteval.h))
$(eval $(call add_include_file,kernel/constids.inc))
$(eval $(call add_include_file,kernel/cost.h))
$(eval $(call add_include_file,kernel/drivertools.h))
$(eval $(call add_include_file,kernel/ff.h))
$(eval $(call add_include_file,kernel/ffinit.h))
$(eval $(call add_include_file,kernel/ffmerge.h))
$(eval $(call add_include_file,kernel/fmt.h))
ifeq ($(ENABLE_ZLIB),1)
$(eval $(call add_include_file,kernel/fstdata.h))
endif
$(eval $(call add_include_file,kernel/gzip.h))
$(eval $(call add_include_file,kernel/hashlib.h))
$(eval $(call add_include_file,kernel/io.h))
$(eval $(call add_include_file,kernel/json.h))
$(eval $(call add_include_file,kernel/log.h))
$(eval $(call add_include_file,kernel/macc.h))
$(eval $(call add_include_file,kernel/modtools.h))
$(eval $(call add_include_file,kernel/mem.h))
$(eval $(call add_include_file,kernel/qcsat.h))
$(eval $(call add_include_file,kernel/register.h))
$(eval $(call add_include_file,kernel/rtlil.h))
$(eval $(call add_include_file,kernel/satgen.h))
$(eval $(call add_include_file,kernel/scopeinfo.h))
$(eval $(call add_include_file,kernel/sexpr.h))
$(eval $(call add_include_file,kernel/sigtools.h))
$(eval $(call add_include_file,kernel/timinginfo.h))
$(eval $(call add_include_file,kernel/utils.h))
$(eval $(call add_include_file,kernel/yosys.h))
$(eval $(call add_include_file,kernel/yosys_common.h))
$(eval $(call add_include_file,kernel/yw.h))
$(eval $(call add_include_file,libs/ezsat/ezsat.h))
$(eval $(call add_include_file,libs/ezsat/ezminisat.h))
ifeq ($(ENABLE_ZLIB),1)
$(eval $(call add_include_file,libs/fst/fstapi.h))
endif
$(eval $(call add_include_file,libs/sha1/sha1.h))
$(eval $(call add_include_file,libs/json11/json11.hpp))
$(eval $(call add_include_file,passes/fsm/fsmdata.h))
$(eval $(call add_include_file,frontends/ast/ast.h))
$(eval $(call add_include_file,frontends/ast/ast_binding.h))
$(eval $(call add_include_file,frontends/blif/blifparse.h))
$(eval $(call add_include_file,backends/rtlil/rtlil_backend.h))

OBJS += kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o kernel/yosys.o kernel/io.o kernel/gzip.o
OBJS += kernel/binding.o kernel/tclapi.o
OBJS += kernel/cellaigs.o kernel/celledges.o kernel/cost.o kernel/satgen.o kernel/scopeinfo.o kernel/qcsat.o kernel/mem.o kernel/ffmerge.o kernel/ff.o kernel/yw.o kernel/json.o kernel/fmt.o kernel/sexpr.o
OBJS += kernel/drivertools.o kernel/functional.o
ifeq ($(ENABLE_ZLIB),1)
OBJS += kernel/fstdata.o
endif
ifeq ($(ENABLE_PLUGINS),1)
ifeq ($(OS), MINGW)
OBJS += libs/dlfcn-win32/dlfcn.o
endif
endif

kernel/log.o: CXXFLAGS += -DYOSYS_SRC='"$(YOSYS_SRC)"'
kernel/yosys.o: CXXFLAGS += -DYOSYS_DATDIR='"$(DATDIR)"' -DYOSYS_PROGRAM_PREFIX='"$(PROGRAM_PREFIX)"'
ifeq ($(ENABLE_ABC),1)
ifneq ($(ABCEXTERNAL),)
kernel/yosys.o: CXXFLAGS += -DABCEXTERNAL='"$(ABCEXTERNAL)"'
endif
endif

OBJS += libs/bigint/BigIntegerAlgorithms.o libs/bigint/BigInteger.o libs/bigint/BigIntegerUtils.o
OBJS += libs/bigint/BigUnsigned.o libs/bigint/BigUnsignedInABase.o

OBJS += libs/sha1/sha1.o

OBJS += libs/json11/json11.o

OBJS += libs/ezsat/ezsat.o
OBJS += libs/ezsat/ezminisat.o

OBJS += libs/minisat/Options.o
OBJS += libs/minisat/SimpSolver.o
OBJS += libs/minisat/Solver.o
OBJS += libs/minisat/System.o

ifeq ($(ENABLE_ZLIB),1)
OBJS += libs/fst/fstapi.o
OBJS += libs/fst/fastlz.o
OBJS += libs/fst/lz4.o
endif

techlibs/%_pm.h: passes/pmgen/pmgen.py techlibs/%.pmg
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $< -o $@ -p $(notdir $*) $(filter-out $<,$^)

ifneq ($(SMALL),1)

OBJS += libs/subcircuit/subcircuit.o

include $(YOSYS_SRC)/frontends/*/Makefile.inc
include $(YOSYS_SRC)/passes/*/Makefile.inc
include $(YOSYS_SRC)/backends/*/Makefile.inc
include $(YOSYS_SRC)/techlibs/*/Makefile.inc

else

include $(YOSYS_SRC)/frontends/verilog/Makefile.inc
ifeq ($(ENABLE_VERIFIC),1)
include $(YOSYS_SRC)/frontends/verific/Makefile.inc
endif
include $(YOSYS_SRC)/frontends/rtlil/Makefile.inc
include $(YOSYS_SRC)/frontends/ast/Makefile.inc
include $(YOSYS_SRC)/frontends/blif/Makefile.inc

OBJS += passes/hierarchy/hierarchy.o
OBJS += passes/cmds/select.o
OBJS += passes/cmds/show.o
OBJS += passes/cmds/stat.o
OBJS += passes/cmds/cover.o
OBJS += passes/cmds/design.o
OBJS += passes/cmds/plugin.o

include $(YOSYS_SRC)/passes/proc/Makefile.inc
include $(YOSYS_SRC)/passes/opt/Makefile.inc
include $(YOSYS_SRC)/passes/techmap/Makefile.inc

include $(YOSYS_SRC)/backends/verilog/Makefile.inc
include $(YOSYS_SRC)/backends/rtlil/Makefile.inc

include $(YOSYS_SRC)/techlibs/common/Makefile.inc

endif

ifeq ($(LINK_ABC),1)
OBJS += $(PROGRAM_PREFIX)yosys-libabc.a
endif

# prevent the CXXFLAGS set by this Makefile from reaching abc/Makefile,
# especially the -MD flag which will break the build when CXX is clang
unexport CXXFLAGS

top-all: $(TARGETS) $(EXTRA_TARGETS)
	@echo ""
	@echo "  Build successful."
	@echo ""

.PHONY: compile-only
compile-only: $(OBJS) $(GENFILES) $(EXTRA_TARGETS)
	@echo ""
	@echo "  Compile successful."
	@echo ""

.PHONY: share
share: $(EXTRA_TARGETS)
	@echo ""
	@echo "  Share directory created."
	@echo ""

$(PROGRAM_PREFIX)yosys$(EXE): $(OBJS)
	$(P) $(CXX) -o $(PROGRAM_PREFIX)yosys$(EXE) $(EXE_LINKFLAGS) $(LINKFLAGS) $(OBJS) $(EXE_LIBS) $(LIBS) $(LIBS_VERIFIC)

libyosys.so: $(filter-out kernel/driver.o,$(OBJS))
ifeq ($(OS), Darwin)
	$(P) $(CXX) -o libyosys.so -shared -undefined dynamic_lookup -Wl,-install_name,$(LIBDIR)/libyosys.so $(LINKFLAGS) $^ $(LIBS) $(LIBS_VERIFIC)
else
	$(P) $(CXX) -o libyosys.so -shared -Wl,-soname,$(LIBDIR)/libyosys.so $(LINKFLAGS) $^ $(LIBS) $(LIBS_VERIFIC)
endif

%.o: %.cc
	$(Q) mkdir -p $(dir $@)
	$(P) $(CXX) -o $@ -c $(CPPFLAGS) $(CXXFLAGS) $<

%.pyh: %.h
	$(Q) mkdir -p $(dir $@)
	$(P) cat $< | grep -E -v "#[ ]*(include|error)" | $(CXX) $(CXXFLAGS) -x c++ -o $@ -E -P -

ifeq ($(ENABLE_PYOSYS),1)
$(PY_WRAPPER_FILE).cc: misc/$(PY_GEN_SCRIPT).py $(PY_WRAP_INCLUDES)
	$(Q) mkdir -p $(dir $@)
	$(P) $(PYTHON_EXECUTABLE) -c "from misc import $(PY_GEN_SCRIPT); $(PY_GEN_SCRIPT).gen_wrappers(\"$(PY_WRAPPER_FILE).cc\")"
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
LIBS_NOVERIFIC = $(foreach v,$(LIBS),$(if $(findstring $(VERIFIC_DIR),$(v)),,$(v)))
else
CXXFLAGS_NOVERIFIC = $(CXXFLAGS)
LIBS_NOVERIFIC = $(LIBS)
endif

$(PROGRAM_PREFIX)yosys-config: misc/yosys-config.in $(YOSYS_SRC)/Makefile
	$(P) $(SED) -e 's#@CXXFLAGS@#$(subst -Ilibs/dlfcn-win32,,$(subst -I. -I"$(YOSYS_SRC)",-I"$(DATDIR)/include",$(strip $(CXXFLAGS_NOVERIFIC))))#;' \
			-e 's#@CXX@#$(strip $(CXX))#;' -e 's#@LINKFLAGS@#$(strip $(LINKFLAGS) $(PLUGIN_LINKFLAGS))#;' -e 's#@LIBS@#$(strip $(LIBS_NOVERIFIC) $(PLUGIN_LIBS))#;' \
			-e 's#@BINDIR@#$(strip $(BINDIR))#;' -e 's#@DATDIR@#$(strip $(DATDIR))#;' < $< > $(PROGRAM_PREFIX)yosys-config
	$(Q) chmod +x $(PROGRAM_PREFIX)yosys-config

.PHONY: check-git-abc

check-git-abc:
	@if [ ! -d "$(YOSYS_SRC)/abc" ] && git -C "$(YOSYS_SRC)" status >/dev/null 2>&1; then \
		echo "Error: The 'abc' directory does not exist."; \
		echo "Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		exit 1; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^ '; then \
		exit 0; \
	elif [ -f "$(YOSYS_SRC)/abc/.gitcommit" ] && ! grep -q '\$$Format:%[hH]\$$' "$(YOSYS_SRC)/abc/.gitcommit"; then \
		echo "'abc' comes from a tarball. Continuing."; \
		exit 0; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^+'; then \
		echo "'abc' submodule does not match expected commit."; \
		echo "Run 'git submodule update' to check out the correct version."; \
		echo "Note: If testing a different version of abc, call 'git commit abc' in the Yosys source directory to update the expected commit."; \
		exit 1; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^U'; then \
		echo "'abc' submodule has merge conflicts."; \
		echo "Please resolve merge conflicts before continuing."; \
		exit 1; \
	elif [ -f "$(YOSYS_SRC)/abc/.gitcommit" ] && grep -q '\$$Format:%[hH]\$$' "$(YOSYS_SRC)/abc/.gitcommit"; then \
		echo "Error: 'abc' is not configured as a git submodule."; \
		echo "To resolve this:"; \
		echo "1. Back up your changes: Save any modifications from the 'abc' directory to another location."; \
		echo "2. Remove the existing 'abc' directory: Delete the 'abc' directory and all its contents."; \
		echo "3. Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		echo "4. Reapply your changes: Move your saved changes back to the 'abc' directory, if necessary."; \
		exit 1; \
	elif ! git -C "$(YOSYS_SRC)" status >/dev/null 2>&1; then \
		echo "$(realpath $(YOSYS_SRC)) is not configured as a git repository, and 'abc' folder is missing."; \
		echo "If you already have ABC, set 'ABCEXTERNAL' make variable to point to ABC executable."; \
		echo "Otherwise, download release archive 'yosys.tar.gz' from https://github.com/YosysHQ/yosys/releases."; \
		echo "    ('Source code' archive does not contain submodules.)"; \
		exit 1; \
	else \
		echo "Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		exit 1; \
	fi

abc/abc$(EXE) abc/libabc.a: | check-git-abc
	$(P)
	$(Q) mkdir -p abc && $(MAKE) -C $(PROGRAM_PREFIX)abc -f "$(realpath $(YOSYS_SRC)/abc/Makefile)" ABCSRC="$(realpath $(YOSYS_SRC)/abc/)" $(S) $(ABCMKARGS) $(if $(filter %.a,$@),PROG="abc",PROG="abc$(EXE)") MSG_PREFIX="$(eval P_OFFSET = 5)$(call P_SHOW)$(eval P_OFFSET = 10) ABC: " $(if $(filter %.a,$@),libabc.a)

$(PROGRAM_PREFIX)yosys-abc$(EXE): abc/abc$(EXE)
	$(P) cp $< $(PROGRAM_PREFIX)yosys-abc$(EXE)

$(PROGRAM_PREFIX)yosys-libabc.a: abc/libabc.a
	$(P) cp $< $(PROGRAM_PREFIX)yosys-libabc.a

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

# Tests that generate .mk with tests/gen-tests-makefile.sh
MK_TEST_DIRS =
MK_TEST_DIRS += tests/arch/anlogic
MK_TEST_DIRS += tests/arch/ecp5
MK_TEST_DIRS += tests/arch/efinix
MK_TEST_DIRS += tests/arch/gatemate
MK_TEST_DIRS += tests/arch/gowin
MK_TEST_DIRS += tests/arch/ice40
MK_TEST_DIRS += tests/arch/intel_alm
MK_TEST_DIRS += tests/arch/machxo2
MK_TEST_DIRS += tests/arch/microchip
MK_TEST_DIRS += tests/arch/nanoxplore
MK_TEST_DIRS += tests/arch/nexus
MK_TEST_DIRS += tests/arch/quicklogic/pp3
MK_TEST_DIRS += tests/arch/quicklogic/qlf_k6n10f
MK_TEST_DIRS += tests/arch/xilinx
MK_TEST_DIRS += tests/opt
MK_TEST_DIRS += tests/sat
MK_TEST_DIRS += tests/sim
MK_TEST_DIRS += tests/svtypes
MK_TEST_DIRS += tests/techmap
MK_TEST_DIRS += tests/various
ifeq ($(ENABLE_VERIFIC),1)
ifneq ($(YOSYS_NOVERIFIC),1)
MK_TEST_DIRS += tests/verific
endif
endif
MK_TEST_DIRS += tests/verilog

# Tests that don't generate .mk
SH_TEST_DIRS =
SH_TEST_DIRS += tests/simple
SH_TEST_DIRS += tests/simple_abc9
SH_TEST_DIRS += tests/hana
SH_TEST_DIRS += tests/asicworld
# SH_TEST_DIRS += tests/realmath
SH_TEST_DIRS += tests/share
SH_TEST_DIRS += tests/opt_share
SH_TEST_DIRS += tests/fsm
SH_TEST_DIRS += tests/memlib
SH_TEST_DIRS += tests/bram
SH_TEST_DIRS += tests/svinterfaces
SH_TEST_DIRS += tests/xprop
SH_TEST_DIRS += tests/select
SH_TEST_DIRS += tests/peepopt
SH_TEST_DIRS += tests/proc
SH_TEST_DIRS += tests/blif
SH_TEST_DIRS += tests/arch
SH_TEST_DIRS += tests/rpc
SH_TEST_DIRS += tests/memfile
SH_TEST_DIRS += tests/fmt
SH_TEST_DIRS += tests/cxxrtl
SH_TEST_DIRS += tests/liberty
ifeq ($(ENABLE_FUNCTIONAL_TESTS),1)
SH_TEST_DIRS += tests/functional
endif

# Tests that don't generate .mk and need special args
SH_ABC_TEST_DIRS =
SH_ABC_TEST_DIRS += tests/memories
SH_ABC_TEST_DIRS += tests/aiger
SH_ABC_TEST_DIRS += tests/alumacc

# seed-tests/ is a dummy string, not a directory
.PHONY: seed-tests
seed-tests: $(SH_TEST_DIRS:%=seed-tests/%)
.PHONY: seed-tests/%
seed-tests/%: %/run-test.sh $(TARGETS) $(EXTRA_TARGETS)
	+cd $* && bash run-test.sh $(SEEDOPT)
	+@echo "...passed tests in $*"

# abcopt-tests/ is a dummy string, not a directory
.PHONY: abcopt-tests
abcopt-tests: $(SH_ABC_TEST_DIRS:%=abcopt-tests/%)
abcopt-tests/%: %/run-test.sh $(TARGETS) $(EXTRA_TARGETS)
	+cd $* && bash run-test.sh $(ABCOPT) $(SEEDOPT)
	+@echo "...passed tests in $*"

# makefile-tests/ is a dummy string, not a directory
.PHONY: makefile-tests
makefile-tests: $(MK_TEST_DIRS:%=makefile-tests/%)
# this target actually emits .mk files
%.mk:
	+cd $(dir $*) && bash run-test.sh
# this one spawns submake on each
makefile-tests/%: %/run-test.mk $(TARGETS) $(EXTRA_TARGETS)
	$(MAKE) -C $* -f run-test.mk
	+@echo "...passed tests in $*"

test: makefile-tests abcopt-tests seed-tests
	@echo ""
	@echo "  Passed \"make test\"."
ifeq ($(ENABLE_VERIFIC),1)
ifeq ($(YOSYS_NOVERIFIC),1)
	@echo "  Ran tests without verific support due to YOSYS_NOVERIFIC=1."
endif
endif
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
	git clone https://github.com/YosysHQ/yosys-tests.git tests/ystests
	+$(MAKE) PATH="$$PWD:$$PATH" -C tests/ystests
	@echo ""
	@echo "  Finished \"make ystests\"."
	@echo ""

# Unit test
unit-test: libyosys.so
	@$(MAKE) -C $(UNITESTPATH) CXX="$(CXX)" CC="$(CC)" CPPFLAGS="$(CPPFLAGS)" \
		CXXFLAGS="$(CXXFLAGS)" LINKFLAGS="$(LINKFLAGS)" LIBS="$(LIBS)" ROOTPATH="$(CURDIR)"

clean-unit-test:
	@$(MAKE) -C $(UNITESTPATH) clean

install: $(TARGETS) $(EXTRA_TARGETS)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(BINDIR)
	$(INSTALL_SUDO) cp $(filter-out libyosys.so,$(TARGETS)) $(DESTDIR)$(BINDIR)
ifneq ($(filter $(PROGRAM_PREFIX)yosys,$(TARGETS)),)
	if [ -n "$(STRIP)" ]; then $(INSTALL_SUDO) $(STRIP) -S $(DESTDIR)$(BINDIR)/$(PROGRAM_PREFIX)yosys; fi
endif
ifneq ($(filter $(PROGRAM_PREFIX)yosys-abc,$(TARGETS)),)
	if [ -n "$(STRIP)" ]; then $(INSTALL_SUDO) $(STRIP) $(DESTDIR)$(BINDIR)/$(PROGRAM_PREFIX)yosys-abc; fi
endif
ifneq ($(filter $(PROGRAM_PREFIX)yosys-filterlib,$(TARGETS)),)
	if [ -n "$(STRIP)" ]; then $(INSTALL_SUDO) $(STRIP) $(DESTDIR)$(BINDIR)/$(PROGRAM_PREFIX)yosys-filterlib; fi
endif
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(DATDIR)
	$(INSTALL_SUDO) cp -r share/. $(DESTDIR)$(DATDIR)/.
ifeq ($(ENABLE_LIBYOSYS),1)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(LIBDIR)
	$(INSTALL_SUDO) cp libyosys.so $(DESTDIR)$(LIBDIR)/
	if [ -n "$(STRIP)" ]; then $(INSTALL_SUDO) $(STRIP) -S $(DESTDIR)$(LIBDIR)/libyosys.so; fi
ifeq ($(ENABLE_PYOSYS),1)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys
	$(INSTALL_SUDO) cp libyosys.so $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys/libyosys.so
	$(INSTALL_SUDO) cp -r share $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys
ifeq ($(ENABLE_ABC),1)
	$(INSTALL_SUDO) cp yosys-abc $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys/yosys-abc
endif
	$(INSTALL_SUDO) cp misc/__init__.py $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys/
endif
endif
ifeq ($(ENABLE_PLUGINS),1)
ifeq ($(OS), MINGW)
	$(INSTALL_SUDO) mkdir -p $(DESTDIR)$(LIBDIR)
	$(INSTALL_SUDO) cp libyosys_exe.a $(DESTDIR)$(LIBDIR)/
endif
endif

uninstall:
	$(INSTALL_SUDO) rm -vf $(addprefix $(DESTDIR)$(BINDIR)/,$(notdir $(TARGETS)))
	$(INSTALL_SUDO) rm -rvf $(DESTDIR)$(DATDIR)
ifeq ($(ENABLE_LIBYOSYS),1)
	$(INSTALL_SUDO) rm -vf $(DESTDIR)$(LIBDIR)/libyosys.so
ifeq ($(ENABLE_PYOSYS),1)
	$(INSTALL_SUDO) rm -vf $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys/libyosys.so
	$(INSTALL_SUDO) rm -vf $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys/__init__.py
	$(INSTALL_SUDO) rmdir $(DESTDIR)$(PYTHON_DESTDIR)/$(subst -,_,$(PROGRAM_PREFIX))pyosys
endif
endif

# also others, but so long as it doesn't fail this is enough to know we tried
docs/source/cmd/abc.rst: $(TARGETS) $(EXTRA_TARGETS)
	$(Q) mkdir -p docs/source/cmd
	$(Q) mkdir -p temp/docs/source/cmd
	$(Q) cd temp && ./../$(PROGRAM_PREFIX)yosys -p 'help -write-rst-command-reference-manual'
	$(Q) $(RSYNC_CP) temp/docs/source/cmd docs/source
	$(Q) rm -rf temp
docs/source/cell/word_add.rst: $(TARGETS) $(EXTRA_TARGETS)
	$(Q) mkdir -p docs/source/cell
	$(Q) mkdir -p temp/docs/source/cell
	$(Q) cd temp && ./../$(PROGRAM_PREFIX)yosys -p 'help -write-rst-cells-manual'
	$(Q) $(RSYNC_CP) temp/docs/source/cell docs/source
	$(Q) rm -rf temp

docs/source/generated/cells.json: docs/source/generated $(TARGETS) $(EXTRA_TARGETS)
	$(Q) ./$(PROGRAM_PREFIX)yosys -p 'help -dump-cells-json $@'

docs/source/generated/%.cc: backends/%.cc
	$(Q) mkdir -p $(@D)
	$(Q) cp $< $@

# diff returns exit code 1 if the files are different, but it's not an error
docs/source/generated/functional/rosette.diff: backends/functional/smtlib.cc backends/functional/smtlib_rosette.cc
	$(Q) mkdir -p $(@D)
	$(Q) diff -U 20 $^ > $@ || exit 0

PHONY: docs/gen/functional_ir
docs/gen/functional_ir: docs/source/generated/functional/smtlib.cc docs/source/generated/functional/rosette.diff

PHONY: docs/gen docs/usage docs/reqs
docs/gen: $(TARGETS)
	$(Q) $(MAKE) -C docs gen

docs/source/generated:
	$(Q) mkdir -p docs/source/generated

# some commands return an error and print the usage text to stderr
define DOC_USAGE_STDERR
docs/source/generated/$(1): $(TARGETS) docs/source/generated FORCE
	-$(Q) ./$(PROGRAM_PREFIX)$(1) --help 2> $$@
endef
DOCS_USAGE_STDERR := yosys-filterlib

# The in-tree ABC (yosys-abc) is only built when ABCEXTERNAL is not set.
ifeq ($(ABCEXTERNAL),)
DOCS_USAGE_STDERR += yosys-abc
endif

$(foreach usage,$(DOCS_USAGE_STDERR),$(eval $(call DOC_USAGE_STDERR,$(usage))))

# others print to stdout
define DOC_USAGE_STDOUT
docs/source/generated/$(1): $(TARGETS) docs/source/generated
	$(Q) ./$(PROGRAM_PREFIX)$(1) --help > $$@ || rm $$@
endef
DOCS_USAGE_STDOUT := yosys yosys-smtbmc yosys-witness yosys-config
$(foreach usage,$(DOCS_USAGE_STDOUT),$(eval $(call DOC_USAGE_STDOUT,$(usage))))

docs/usage: $(addprefix docs/source/generated/,$(DOCS_USAGE_STDOUT) $(DOCS_USAGE_STDERR))

docs/reqs:
	$(Q) $(MAKE) -C docs reqs

.PHONY: docs/prep
docs/prep: docs/source/cmd/abc.rst docs/source/generated/cells.json docs/gen docs/usage docs/gen/functional_ir

DOC_TARGET ?= html
docs: docs/prep
	$(Q) $(MAKE) -C docs $(DOC_TARGET)

clean:
	rm -rf share
	rm -rf kernel/*.pyh
	rm -f $(OBJS) $(GENFILES) $(TARGETS) $(EXTRA_TARGETS) $(EXTRA_OBJS) $(PY_WRAP_INCLUDES) $(PY_WRAPPER_FILE).cc
	rm -f kernel/version_*.o kernel/version_*.cc
	rm -f kernel/python_wrappers.o
	rm -f libs/*/*.d frontends/*/*.d passes/*/*.d backends/*/*.d kernel/*.d techlibs/*/*.d
	rm -rf tests/asicworld/*.out tests/asicworld/*.log
	rm -rf tests/hana/*.out tests/hana/*.log
	rm -rf tests/simple/*.out tests/simple/*.log
	rm -rf tests/memories/*.out tests/memories/*.log tests/memories/*.dmp
	rm -rf tests/sat/*.log tests/techmap/*.log tests/various/*.log
	rm -rf tests/bram/temp tests/fsm/temp tests/realmath/temp tests/share/temp tests/smv/temp tests/various/temp
	rm -rf vloghtb/Makefile vloghtb/refdat vloghtb/rtl vloghtb/scripts vloghtb/spec vloghtb/check_yosys vloghtb/vloghammer_tb.tar.bz2 vloghtb/temp vloghtb/log_test_*
	rm -f tests/svinterfaces/*.log_stdout tests/svinterfaces/*.log_stderr tests/svinterfaces/dut_result.txt tests/svinterfaces/reference_result.txt tests/svinterfaces/a.out tests/svinterfaces/*_syn.v tests/svinterfaces/*.diff
	rm -f  tests/tools/cmp_tbdata
	rm -f $(addsuffix /run-test.mk,$(MK_TEST_DIRS))
	-$(MAKE) -C docs clean
	rm -rf docs/source/cmd docs/util/__pycache__
	rm -f *.whl
	rm -f libyosys.so

clean-abc:
	$(MAKE) -C abc DEP= clean
	rm -f $(PROGRAM_PREFIX)yosys-abc$(EXE) $(PROGRAM_PREFIX)yosys-libabc.a abc/abc-[0-9a-f]* abc/libabc-[0-9a-f]*.a

mrproper: clean
	git clean -xdf

coverage:
	./$(PROGRAM_PREFIX)yosys -qp 'help; help -all'
	rm -rf coverage.info coverage_html
	lcov --capture -d . --no-external -o coverage.info
	genhtml coverage.info --output-directory coverage_html

clean_coverage:
	find . -name "*.gcda" -type f -delete

FUNC_KERNEL := functional.cc functional.h sexpr.cc sexpr.h compute_graph.h
FUNC_INCLUDES := $(addprefix --include *,functional/* $(FUNC_KERNEL))
coverage_functional:
	rm -rf coverage.info coverage_html
	lcov --capture -d backends/functional -d kernel $(FUNC_INCLUDES) --no-external -o coverage.info
	genhtml coverage.info --output-directory coverage_html

qtcreator:
	echo "$(CXXFLAGS)" | grep -o '\-D[^ ]*' | tr ' ' '\n' | sed 's/-D/#define /' | sed 's/=/ /'> qtcreator.config
	{ for file in $(basename $(OBJS)); do \
		for prefix in cc y l; do if [ -f $${file}.$${prefix} ]; then echo $$file.$${prefix}; fi; done \
	done; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \); } > qtcreator.files
	{ echo .; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \) -printf '%h\n' | sort -u; } > qtcreator.includes
	touch qtcreator.creator

vcxsrc: $(GENFILES) $(EXTRA_TARGETS)
	rm -rf yosys-win32-vcxsrc-$(YOSYS_VER){,.zip}
	set -e; for f in `ls $(filter %.cc %.cpp,$(GENFILES)) $(addsuffix .cc,$(basename $(OBJS))) $(addsuffix .cpp,$(basename $(OBJS))) 2> /dev/null`; do \
		echo "Analyse: $$f" >&2; cpp -std=c++17 -MM -I. -D_YOSYS_ $$f; done | sed 's,.*:,,; s,//*,/,g; s,/[^/]*/\.\./,/,g; y, \\,\n\n,;' | grep '^[^/]' | sort -u | grep -v kernel/version_ > srcfiles.txt
	echo "libs/fst/fst_win_unistd.h" >> srcfiles.txt
	bash misc/create_vcxsrc.sh yosys-win32-vcxsrc $(YOSYS_VER) $(GIT_REV)
	echo "namespace Yosys { extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys (Version Information Unavailable)\"; }" > kernel/version.cc
	zip yosys-win32-vcxsrc-$(YOSYS_VER)/genfiles.zip $(GENFILES) kernel/version.cc
	zip -r yosys-win32-vcxsrc-$(YOSYS_VER).zip yosys-win32-vcxsrc-$(YOSYS_VER)/
	rm -f srcfiles.txt kernel/version.cc

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

config-wasi: clean
	echo 'CONFIG := wasi' > Makefile.conf
	echo 'ENABLE_TCL := 0' >> Makefile.conf
	echo 'ENABLE_ABC := 0' >> Makefile.conf
	echo 'ENABLE_PLUGINS := 0' >> Makefile.conf
	echo 'ENABLE_READLINE := 0' >> Makefile.conf
	echo 'ENABLE_ZLIB := 0' >> Makefile.conf

config-msys2-32: clean
	echo 'CONFIG := msys2-32' > Makefile.conf
	echo "PREFIX := $(MINGW_PREFIX)" >> Makefile.conf

config-msys2-64: clean
	echo 'CONFIG := msys2-64' > Makefile.conf
	echo "PREFIX := $(MINGW_PREFIX)" >> Makefile.conf

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

echo-cxx:
	@echo "$(CXX)"

-include libs/*/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d
-include techlibs/*/*.d

FORCE:

.PHONY: all top-all abc test install install-abc docs clean mrproper qtcreator coverage vcxsrc
.PHONY: config-clean config-clang config-gcc config-gcc-static config-gprof config-sudo
