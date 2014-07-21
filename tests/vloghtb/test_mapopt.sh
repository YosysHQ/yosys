#!/bin/bash

set -e
source common.sh

f=$1
n=$(basename ${f%.v})

test_equiv mapopt "opt -fine; techmap; opt" "-set-def-inputs" $n $f

exit 0
