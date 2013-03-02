
CONFIG := clang-debug
# CONFIG := gcc-debug
# CONFIG := profile
# CONFIG := release

CC = clang
CXX = clang
CXXFLAGS = -MD -Wall -Wextra -ggdb
LDLIBS = -lstdc++

ifeq ($(CONFIG),clang-debug)
CXXFLAGS += -std=c++11 -O0
endif

ifeq ($(CONFIG),gcc-debug)
CC = gcc
CXX = gcc
CXXFLAGS += -std=gnu++0x -O0
endif

ifeq ($(CONFIG),profile)
CC = gcc
CXX = gcc
CXXFLAGS += -std=gnu++0x -Os -DNDEBUG
endif

ifeq ($(CONFIG),release)
CC = gcc
CXX = gcc
CXXFLAGS += -std=gnu++0x -march=native -O3 -DNDEBUG
endif

all: demo scshell

demo: demo.o subcircuit.o

scshell: scshell.o subcircuit.o

test: scshell
	./scshell < test_macc22.txt
	./scshell < test_mine.txt
	perl test_perm.pl | ./scshell
	splrun test_shorts.spl | ./scshell
	splrun test_large.spl | ./scshell

clean:
	rm -f demo scshell *.o *.d

.PHONY: all test clean

-include *.d

