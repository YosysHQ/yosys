#!/usr/bin/env bash

run() {
    alt=$1
    span=$2
    left=$3
    right=$4
    echo "a=$alt s=$span l=$left r=$right"

    ../../yosys -q \
        -DALT=$alt \
        -DSPAN=$span \
        -DLEFT=$left \
        -DRIGHT=$right \
        -p "read_verilog dynamic_range_lhs.v" \
        -p "proc" \
        -p "equiv_make gold gate equiv" \
        -p "equiv_simple -undef" \
        -p "equiv_status -assert"
}

trap 'echo "ERROR in dynamic_range_lhs.sh span=$span left=$left right=$right" >&2; exit 1' ERR

for alt in `seq 0 1`; do
for span in `seq 1 4`; do
for left in `seq -4 4`; do
for right in `seq $(expr $left + -3) $(expr $left + 3)`; do
    run $alt $span $left $right
done
done
done
done
