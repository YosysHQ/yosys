#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
echo "Generate FST for sim models"
find tb/* -name tb*.v | while read name; do
    test_name=$(basename $name .v)
    echo "Test $test_name"
    verilog_name=${test_name:3}.v
    iverilog -o tb/$test_name.out $name $verilog_name
    ./tb/$test_name.out -fst
done
run_tests --yosys-scripts --bash --yosys-args "-w 'Yosys has only limited support for tri-state logic at the moment.'"
