#!/bin/bash

set -ev

../../yosys -b 'verilog -noattr' -o mem_simple_4x1_synth.v -p 'proc; opt; memory -nomap; techmap -map mem_simple_4x1_map.v;; techmap; opt; abc;; stat' mem_simple_4x1_uut.v

iverilog -o mem_simple_4x1_gold_tb mem_simple_4x1_tb.v mem_simple_4x1_uut.v
iverilog -o mem_simple_4x1_gate_tb mem_simple_4x1_tb.v mem_simple_4x1_synth.v mem_simple_4x1_cells.v

./mem_simple_4x1_gold_tb > mem_simple_4x1_gold_tb.out
./mem_simple_4x1_gate_tb > mem_simple_4x1_gate_tb.out

diff -u mem_simple_4x1_gold_tb.out mem_simple_4x1_gate_tb.out
rm -f mem_simple_4x1_synth.v mem_simple_4x1_tb.vcd
rm -f mem_simple_4x1_{gold,gate}_tb{,.out}
: OK

