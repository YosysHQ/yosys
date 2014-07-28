#!/bin/bash

set -e
source common.sh

f=$1
n=$(basename ${f%.v})

mkdir -p log_test_mapopt
rm -f log_test_mapopt/$n.*

test_equiv mapopt_1 "opt -fine; techmap; opt" "-set-def-inputs" $n $f
test_autotest mapopt_2 "proc; opt; techmap; opt" $n $f

tail -n20 log_test_mapopt_1/$n.txt log_test_mapopt_2/$n.txt > log_test_mapopt/$n.txt

exit 0
