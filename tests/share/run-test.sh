#!/bin/bash
set -e

rm -rf temp
mkdir -p temp
echo "generating tests.."
python generate.py

echo "running tests.."
for i in $( ls temp/*.ys | sed 's,[^0-9],,g; s,^0*\(.\),\1,g;' ); do
	echo -n "[$i]"
	idx=$( printf "%05d" $i )
	../../yosys -ql temp/uut_${idx}.log temp/uut_${idx}.ys
done
echo

