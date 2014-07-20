
CC = clang
CXX = clang
CXXFLAGS = -MD -Wall -Wextra -ggdb
CXXFLAGS += -std=c++11 -O0
LDLIBS = ../minisat/Options.cc ../minisat/SimpSolver.cc ../minisat/Solver.cc ../minisat/System.cc -lm -lstdc++


all: demo_vec demo_bit demo_cmp testbench puzzle3d

demo_vec: demo_vec.o ezsat.o ezminisat.o
demo_bit: demo_bit.o ezsat.o ezminisat.o
demo_cmp: demo_cmp.o ezsat.o ezminisat.o
testbench: testbench.o ezsat.o ezminisat.o
puzzle3d: puzzle3d.o ezsat.o ezminisat.o

test: all
	./testbench
	./demo_bit
	./demo_vec
	# ./demo_cmp
	# ./puzzle3d

clean:
	rm -f demo_bit demo_vec demo_cmp testbench puzzle3d *.o *.d

.PHONY: all test clean

-include *.d

