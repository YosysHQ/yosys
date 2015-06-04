#!/bin/bash
set -e
../../yosys -qq -p "proc; opt; memory -nomap -bram temp/brams_${2}.txt; opt -fast -full; write_verilog temp/synth_${1}_${2}_stage0.v" \
		-l temp/synth_${1}_${2}_stage0.log temp/brams_${1}.v
../../yosys -qq -p "proc; opt; memory -nomap; opt -fast -full; write_verilog -nomem temp/synth_${1}_${2}.v" \
		-l temp/synth_${1}_${2}.log temp/synth_${1}_${2}_stage0.v
iverilog -Dvcd_file=\"temp/tb_${1}_${2}.vcd\" -DSIMLIB_MEMDELAY=1ns -o temp/tb_${1}_${2}.tb temp/brams_${1}_tb.v \
		temp/brams_${1}_ref.v temp/synth_${1}_${2}.v temp/brams_${2}.v ../../techlibs/common/simlib.v
temp/tb_${1}_${2}.tb > temp/tb_${1}_${2}.txt
if grep -q ERROR temp/tb_${1}_${2}.txt; then
	grep -HC2 ERROR temp/tb_${1}_${2}.txt | head
	exit 1
fi
exit 0
