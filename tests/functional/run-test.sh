#!/bin/bash

set -ex

# Loop through all Verilog files in the verilog directory
for verilog_file in verilog/*.v; do
    # Run yosys to process each Verilog file
    ../../yosys -p "read_verilog $verilog_file; write_cxxrtl my_module_cxxrtl.cc; write_functional_cxx my_module_functional_cxx.cc"

    # Compile the generated C++ files with vcd_harness.cpp
    ${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cpp -I ../../backends/functional/cxx_runtime/ -I ../../backends/cxxrtl/runtime/ -o vcd_harness

    # Generate VCD files cxxrtl.vcd and functional_cxx.vcd
    ./vcd_harness

    # Run vcdiff and capture the output
    output=$(vcdiff cxxrtl.vcd functional_cxx.vcd)

    # Check if there is any output
    if [ -n "$output" ]; then
        echo "Differences detected in $verilog_file:"
        echo "$output"
        exit 1
    else
        echo "No differences detected in $verilog_file."
    fi
done

# If all files are processed without differences
exit 0
