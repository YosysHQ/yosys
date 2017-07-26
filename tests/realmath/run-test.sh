#!/bin/bash
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

cd temp
echo "running tests.."
for ((i = 0; i < $count; i++)); do
	echo -n "[$i]"
	idx=$( printf "%05d" $i )
	../../../yosys -qq uut_${idx}.ys
	iverilog -o uut_${idx}_tb uut_${idx}_tb.v uut_${idx}.v uut_${idx}_syn.v
	./uut_${idx}_tb | tee uut_${idx}.err
	if test -s uut_${idx}.err; then
		echo "Note: Make sure that 'iverilog' is an up-to-date git checkout of Icarus Verilog."
		exit 1
	fi
	rm -f uut_${idx}.err
done
echo

