#!/bin/bash
set -ex
../../yosys -q -o async_syn.v -p 'synth; rename uut syn' async.v
iverilog -o async_sim -DTESTBENCH async.v async_syn.v
vvp -N async_sim > async.out
rm -f async_syn.v async_sim async.out async.vcd
