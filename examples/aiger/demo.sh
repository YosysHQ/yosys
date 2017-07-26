#!/bin/bash
set -ex
yosys -p '
	read_verilog -formal demo.v
	prep -flatten -nordff -top demo
	write_smt2 -wires demo.smt2
	flatten demo; delete -output
	memory_map; opt -full
	techmap; opt -fast
	abc -fast -g AND; opt_clean
	write_aiger -map demo.aim demo.aig
'
super_prove demo.aig > demo.aiw
yosys-smtbmc --dump-vcd demo.vcd --aig demo demo.smt2
