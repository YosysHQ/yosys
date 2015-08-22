#!/bin/bash

# run this test many times:
# time bash -c 'for ((i=0; i<100; i++)); do echo "-- $i --"; bash run-test.sh || exit 1; done'

set -e

rm -rf temp
mkdir -p temp
echo "generating tests.."
python3 generate.py

echo "running tests.."
for i in $( ls temp/*.ys | sed 's,[^0-9],,g; s,^0*\(.\),\1,g;' ); do
	echo -n "[$i]"
	idx=$( printf "%05d" $i )
	../../yosys -ql temp/uut_${idx}.log temp/uut_${idx}.ys
done
echo

failed_share=$( echo $( gawk '/^#job#/ { j=$2; db[j]=0; } /^Removing [246] cells/ { delete db[j]; } END { for (j in db) print(j); }' temp/all_share_log.txt ) )
if [ -n "$failed_share" ]; then
	echo "Resource sharing failed for the following test cases: $failed_share"
	false
fi

exit 0
