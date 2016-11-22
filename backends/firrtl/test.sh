#!/bin/bash
set -ex

cd ../../
make
cd backends/firrtl

../../yosys -q -p 'prep -nordff; write_firrtl test.fir' $1

firrtl -i test.fir -o test_out.v -ll Info

../../yosys -p "
	read_verilog $1
	rename Top gold

	read_verilog test_out.v
	rename Top gate

	prep
	memory_map
	miter -equiv -flatten gold gate miter
	hierarchy -top miter

	sat -verify -prove trigger 0 -set-init-zero -seq 10 miter
"
