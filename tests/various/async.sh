#!/usr/bin/env bash
set -ex
../../yosys -q -o async_syn.v -r uut -p 'synth; rename uut syn' async.v
../../yosys -q -o async_prp.v -r uut -p 'prep; rename uut prp' async.v
../../yosys -q -o async_a2s.v -r uut -p 'prep; async2sync; rename uut a2s' async.v
../../yosys -q -o async_ffl.v -r uut -p 'prep; clk2fflogic; rename uut ffl' async.v
iverilog -o async_sim -DTESTBENCH async.v async_???.v
vvp -N async_sim > async.out
tail async.out
grep PASS async.out
rm -f async_???.v async_sim async.out async.vcd
