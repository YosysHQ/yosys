#!/usr/bin/env bash
set -e

# TODO: when sim gets native $check support, remove the -DNO_ASSERT here
echo Running yosys sim
../../yosys -q -p "
read_verilog -formal -DNO_ASSERT clk2fflogic_effects.sv
hierarchy -top top; proc;;

tee -q -o clk2fflogic_effects.sim.log sim -q -n 32
"
echo Running yosys clk2fflogic sim
../../yosys -q -p "
read_verilog -formal clk2fflogic_effects.sv
hierarchy -top top; proc;;
clk2fflogic;;

logger -nowarn ^Assertion
tee -q -o clk2fflogic_effects.clk2fflogic.log sim -q -n 32
"

echo Running iverilog sim
iverilog -g2012 -DNO_ASSERT -o clk2fflogic_effects.iv.out clk2fflogic_effects.sv


./clk2fflogic_effects.iv.out > clk2fflogic_effects.iv.log

gawk '/([0-9]+):/{T=$1;print};/^Failed/{print T,$0}' clk2fflogic_effects.iv.log | sort > clk2fflogic_effects.iv.sorted.log
gawk '/([0-9]+):/{T=$1;print};/^Failed/{print T,$0}' clk2fflogic_effects.sim.log | sort > clk2fflogic_effects.sim.sorted.log
gawk '/([0-9]+):/{T=$1;print};/^Failed/{print T,$0}' clk2fflogic_effects.clk2fflogic.log | sort > clk2fflogic_effects.clk2fflogic.sorted.log

echo Comparing iverilog sim vs yosys sim
cmp clk2fflogic_effects.iv.sorted.log clk2fflogic_effects.sim.sorted.log
echo Comparing iverilog sim vs yosys clk2fflogic sim
cmp clk2fflogic_effects.iv.sorted.log clk2fflogic_effects.clk2fflogic.sorted.log
