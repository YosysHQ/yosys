#!/bin/bash

# run this test many times:
# time bash -c 'for ((i=0; i<100; i++)); do echo "-- $i --"; bash run-test.sh || exit 1; done'

OPTIND=1
count=100
seed=""    # default to no seed specified
verbose=0
while getopts "c:S:v" opt
do
    case "$opt" in
	c) count="$OPTARG" ;;
	S) seed="-S $OPTARG" ;;
	v) verbose="1" ;;
    esac
done
shift "$((OPTIND-1))"

rm -rf temp
mkdir -p temp
echo "generating tests.."
python3 generate.py -c $count $seed

cd temp
echo -n "running tests.. "
if test $verbose -gt 0; then
	echo
fi
failed=0
passed=0
for i in $( ls *.ys | sed 's,[^0-9],,g; s,^0*\(.\),\1,g;' ); do
	if test $verbose -gt 0; then
		echo -n "Test: share[$i] -> "
	fi
	idx=$( printf "%05d" $i )
	../../../yosys -ql uut_${idx}.log uut_${idx}.ys || exit 1

	grep -q '^Removing [246] cells' uut_${idx}_share_log.txt
	test_exit_code=$?
	if test $verbose -gt 0; then
		if test $test_exit_code -ne 0; then
			echo "fail"
			echo "---------------------"
			cat uut_${idx}.log
			echo "---------------------"
		else
			echo "ok"
		fi
	else
		if test $test_exit_code -ne 0; then
			echo -n "F"
		else
			echo -n "."
		fi
	fi
	if test $test_exit_code -ne 0; then
		failed=$(($failed + 1))
	else
		passed=$(($passed + 1))
	fi
done
echo
echo "$count tests run, $passed passed, $failed failed."

if test $failed -ne 0; then
	exit 1
fi
