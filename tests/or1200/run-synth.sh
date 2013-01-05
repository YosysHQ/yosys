#!/bin/bash
time ../../yosys -b "verilog -noexpr" -o synth.v -tl synth.log -s run-synth.ys rtl/or1200_*.v 2>&1 | egrep '^\[[0-9.]+\] (ERROR|--|[0-9]+\.)'
