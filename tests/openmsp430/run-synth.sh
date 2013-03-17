#!/bin/bash
time ../../yosys -b "verilog -noexpr" -o synth.v -tl synth.log -s run-synth.ys \
		rtl/omsp_*.v rtl/openMSP430.v 2>&1 | egrep '^\[[0-9.]+\] (ERROR|-- |[0-9]+\.)'
