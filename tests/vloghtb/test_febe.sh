#!/bin/bash

set -e
source common.sh

f=$1
n=$(basename ${f%.v})

test_febe vlog1 "synth"                   ".v"    "write_verilog" "read_verilog"         "-ignore_div_by_zero" $n $f
test_febe vlog2 "synth -run coarse"       ".v"    "write_verilog" "read_verilog -icells" "-ignore_div_by_zero" $n $f
test_febe blif  "synth; splitnets -ports" ".blif" "write_blif"    "read_blif"            "-ignore_div_by_zero" $n $f

exit 0
