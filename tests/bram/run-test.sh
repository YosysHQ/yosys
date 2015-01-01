#!/bin/bash

# run this test many times:
# time bash -c 'for ((i=0; i<100; i++)); do echo "-- $i --"; bash run-test.sh || exit 1; done'

set -e
rm -rf temp
mkdir -p temp

echo "generating tests.."
python generate.py

{
	echo -n "all:"
	for i in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' ); do
	for j in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' | grep -v $i ); do
		echo -n " temp/job_$i$j.ok"
	done; done
	echo
	for i in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' ); do
	for j in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' | grep -v $i ); do
		echo "temp/job_$i$j.ok:"
		echo "	@bash run-single.sh $i $j"
		echo "	@echo 'Passed test $i vs $j.'"
		echo "	@touch \$@"
	done; done
} > temp/makefile

echo "running tests.."
${MAKE:-make} -f temp/makefile

exit 0
