#!/bin/bash
set -e
../../yosys -qq -p "proc; opt; memory -nomap; memory_bram -rules temp/brams_${2}.txt; opt -fast -full" \
		-l temp/synth_${1}_${2}.log -o temp/synth_${1}_${2}.v temp/brams_${1}.v
iverilog -o temp/tb_${1}_${2}.tb temp/brams_${1}_tb.v temp/brams_${1}_ref.v \
		temp/synth_${1}_${2}.v temp/brams_${2}.v ../../techlibs/common/simlib.v
temp/tb_${1}_${2}.tb > temp/tb_${1}_${2}.txt
if grep -H -C1 ERROR temp/tb_${1}_${2}.txt; then exit 1; fi
exit 0
