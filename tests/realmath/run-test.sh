#!/bin/bash

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
for ((i = 0; i < $count; i++)); do
	if test $verbose -gt 0; then
		echo -n "Test: realmath[$i] -> "
	fi
	idx=$( printf "%05d" $i )
	../../../yosys -qq uut_${idx}.ys || exit 1
	iverilog -o uut_${idx}_tb uut_${idx}_tb.v uut_${idx}.v uut_${idx}_syn.v
	if test ! -s ./uut_${idx}_tb; then
		echo "Note: Make sure that 'iverilog' is an up-to-date git checkout of Icarus Verilog."
		exit 1
	fi
	./uut_${idx}_tb > uut_${idx}.err
	test_exit_code=$?
	if test $verbose -gt 0; then
		if test $test_exit_code -ne 0; then
			echo "fail"
			echo "---------------------"
			cat uut_${idx}.err
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
	rm -f uut_${idx}.err uut_${idx}_tb
done
echo
echo "$count tests run, $passed passed, $failed failed."

if test $failed -ne 0; then
	exit 1
fi
