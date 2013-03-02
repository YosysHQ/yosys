
CONFIG := clang-debug
# CONFIG := gcc-debug
# CONFIG := release

OBJS  = kernel/driver.o kernel/register.o kernel/rtlil.o kernel/log.o kernel/calc.o kernel/select.o kernel/show.o

OBJS += libs/bigint/BigIntegerAlgorithms.o libs/bigint/BigInteger.o libs/bigint/BigIntegerUtils.o
OBJS += libs/bigint/BigUnsigned.o libs/bigint/BigUnsignedInABase.o

OBJS += libs/sha1/sha1.o
OBJS += libs/subcircuit/subcircuit.o

GENFILES =
TARGETS = yosys

all: top-all

CXXFLAGS = -Wall -Wextra -ggdb -I$(shell pwd) -MD -D_YOSYS_
LDFLAGS =
LDLIBS = -lstdc++ -lreadline -lm

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

include frontends/*/Makefile.inc
include passes/*/Makefile.inc
include backends/*/Makefile.inc
include techlibs/Makefile.inc

top-all: $(TARGETS)

yosys: $(OBJS)
	$(CXX) -o yosys $(LDFLAGS) $(OBJS) $(LDLIBS)

test: yosys
	cd tests/simple && bash run-test.sh
	cd tests/hana && bash run-test.sh
	cd tests/asicworld && bash run-test.sh

install: yosys
	install yosys /usr/local/bin/yosys

clean:
	rm -f $(OBJS) $(GENFILES) $(TARGETS)
	rm -f bigint/*.d frontends/*/*.d passes/*/*.d backends/*/*.d kernel/*.d

mrproper: clean
	git clean -xdf

qtcreator:
	{ for file in $(basename $(OBJS)); do \
		for prefix in cc y l; do if [ -f $${file}.$${prefix} ]; then echo $$file.$${prefix}; fi; done \
	done; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \); } > qtcreator.files
	{ echo .; find backends frontends kernel libs passes -type f \( -name '*.h' -o -name '*.hh' \) -printf '%h\n' | sort -u; } > qtcreator.includes
	touch qtcreator.config qtcreator.creator

-include bigint/*.d
-include frontends/*/*.d
-include passes/*/*.d
-include backends/*/*.d
-include kernel/*.d

