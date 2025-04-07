#!/bin/bash

set -ex

run_subtest () {
    local subtest=$1; shift

    ${CC:-gcc} -std=c++11 -O2 -o cxxrtl-test-${subtest} -I../../backends/cxxrtl/runtime test_${subtest}.cc -lstdc++
    ./cxxrtl-test-${subtest}
}

run_subtest value
run_subtest value_fuzz

# Compile-only test.
../../yosys -p "read_verilog test_unconnected_output.v; proc; clean; write_cxxrtl cxxrtl-test-unconnected_output.cc"
${CC:-gcc} -std=c++11 -c -o cxxrtl-test-unconnected_output -I../../backends/cxxrtl/runtime cxxrtl-test-unconnected_output.cc
