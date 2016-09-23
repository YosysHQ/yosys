#!/bin/bash

# run this test many times:
# time bash -c 'for ((i=0; i<100; i++)); do echo "-- $i --"; bash run-test.sh || exit 1; done'

set -e

OPTIND=1
count=100
seed=""    # default to no seed specified
while getopts "c:S:" opt
do
    case "$opt" in
	c) count="$OPTARG" ;;
	S) seed="-S $OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

rm -rf temp
mkdir -p temp
echo "generating tests.."
python3 generate.py -c $count $seed

{
	all_targets="all_targets:"
	echo "all: all_targets"
	echo "	@echo"
	for i in $( ls temp/*.ys | sed 's,[^0-9],,g; s,^0*\(.\),\1,g;' ); do
		idx=$( printf "%05d" $i )
		echo "temp/uut_${idx}.log: temp/uut_${idx}.ys temp/uut_${idx}.v"
		echo "	@echo -n '[$i]'"
		echo "	@../../yosys -ql temp/uut_${idx}.out temp/uut_${idx}.ys"
		echo "	@mv temp/uut_${idx}.out temp/uut_${idx}.log"
		echo "	@grep -q 'SAT proof finished' temp/uut_${idx}.log && echo -n K || echo -n T"
		all_targets="$all_targets temp/uut_${idx}.log"
	done
	echo "$all_targets"
} > temp/makefile

echo "running tests.."
${MAKE:-make} -f temp/makefile

exit 0
