#!/usr/bin/env bash
set -ex

../../yosys -p "
read_verilog -formal -DFAST clk2fflogic_effects.sv
hierarchy -top top; proc;;
tee -o clk2fflogic_effects.sim.log sim -fst /tmp/sim.fst -q -n 16
"

../../yosys -p "
read_verilog -formal -DFAST clk2fflogic_effects.sv
hierarchy -top top; proc;;
clk2fflogic;;

tee -o clk2fflogic_effects.clk2fflogic.log sim -fst /tmp/sim.fst -q -n 16
"

iverilog -g2012 -o clk2fflogic_effects.iv.out clk2fflogic_effects.sv

./clk2fflogic_effects.iv.out > clk2fflogic_effects.iv.log

sort clk2fflogic_effects.iv.log > clk2fflogic_effects.iv.sorted.log
tail +3 clk2fflogic_effects.sim.log | sort > clk2fflogic_effects.sim.sorted.log
tail +3 clk2fflogic_effects.clk2fflogic.log | sort > clk2fflogic_effects.clk2fflogic.sorted.log

cmp clk2fflogic_effects.iv.sorted.log clk2fflogic_effects.sim.sorted.log
cmp clk2fflogic_effects.iv.sorted.log clk2fflogic_effects.clk2fflogic.sorted.log
