#!/bin/bash

set -e
source common.sh

f=$1
n=$(basename ${f%.v})

test_equiv mapopt_1 "opt -fine; techmap; opt" "-set-def-inputs" $n $f
test_autotest mapopt_2 $n $f -p "opt; techmap -extern; opt"

exit 0
