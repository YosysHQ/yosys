#!/bin/bash

set -ex

../../yosys -p "read_verilog verilog/and.v; write_cxxrtl and_cxxrtl.cc; write_functional_cxx and_functional_cxx.cc"
${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cpp -I ../../backends/functional/cxx_runtime/ -I ../../backends/cxxrtl/runtime/ -o vcd_harness
# Generate VCD files cxxrtl.vcd and functional_cxx.vcd
./vcd_harness
# Run vcdiff and capture the output
output=$(vcdiff cxxrtl.vcd functional_cxx.vcd)

# Check if there is any output
if [ -n "$output" ]; then
    echo "Differences detected:"
    echo "$output"
    exit 1
else
    echo "No differences detected."
    exit 0
fi
