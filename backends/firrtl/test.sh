#!/bin/bash
set -ex

../../yosys -p 'prep; write_firrtl test.fir' test.v

firrtl -i test.fir -o test_out.v

../../yosys -p '
	read_verilog test.v
	rename test gold

	read_verilog test_out.v
	rename test gate

	prep
	miter -equiv -flatten gold gate miter
	hierarchy -top miter

	sat -verify -prove trigger 0 -set-init-zero -seq 10 miter
'

