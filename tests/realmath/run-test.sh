#!/bin/bash
set -e

rm -rf temp
mkdir -p temp
echo "generating tests.."
python generate.py

cd temp
echo "running tests.."
for ((i = 0; i < 100; i++)); do
	echo -n "[$i]"
	idx=$( printf "%05d" $i )
	../../../yosys -q uut_${idx}.ys
	iverilog -o uut_${idx}_tb uut_${idx}_tb.v uut_${idx}.v uut_${idx}_syn.v
	./uut_${idx}_tb
done
echo

