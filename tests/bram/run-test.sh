#!/bin/bash

# run this test many times:
# MAKE="make -j8" time bash -c 'for ((i=0; i<100; i++)); do echo "-- $i --"; bash run-test.sh || exit 1; done'

set -e
rm -rf temp
mkdir -p temp

echo "generating tests.."
python3 generate.py

{
	echo -n "all:"
	for i in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' ); do
	for j in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' | grep -v $i ); do
		echo -n " temp/job_${i}_${j}.ok"
	done; done
	echo
	for i in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' ); do
	for j in $( ls temp/brams_*.txt | sed 's,.*_,,; s,\..*,,;' | grep -v $i ); do
		echo "temp/job_${i}_${j}.ok:"
		echo "	@bash run-single.sh ${i} ${j}"
		echo "	@echo 'Passed memory_bram test ${i}_${j}.'"
		echo "	@touch \$@"
	done; done
} > temp/makefile

echo "running tests.."
${MAKE:-make} -f temp/makefile

exit 0
