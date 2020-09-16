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
	echo ".PHONY: all"
	echo "all:"

	for i in $( ls temp/*.ys | sed 's,[^0-9],,g; s,^0*\(.\),\1,g;' ); do
		idx=$( printf "%05d" $i )
		echo ".PHONY: test-$idx"
		echo "all: test-$idx"
		echo "test-$idx:"
		printf "\t@%s\n" \
			"echo -n [$i]" \
			"../../yosys -ql temp/uut_${idx}.log temp/uut_${idx}.ys"
	done
} > temp/makefile

echo "running tests.."
${MAKE:-make} -f temp/makefile
echo

failed_share=$( echo $( gawk '/^#job#/ { j=$2; db[j]=0; } /^Removing [246] cells/ { delete db[j]; } END { for (j in db) print(j); }' temp/all_share_log.txt ) )
if [ -n "$failed_share" ]; then
	echo "Resource sharing failed for the following test cases: $failed_share"
	false
fi

exit 0
