#!/bin/bash

set -ex

# Initialize an array to store the names of failing Verilog files and their failure types
declare -A failing_files

# Loop through all Verilog files in the verilog directory
for verilog_file in verilog/*.v; do
    # Extract the base name without extension
    base_name=$(basename "$verilog_file" .v)
    
    # Run yosys to process each Verilog file
    if ../../yosys -p "read_verilog $verilog_file; write_cxxrtl my_module_cxxrtl.cc; write_functional_cxx my_module_functional_cxx.cc"; then
        echo "Yosys processed $verilog_file successfully."
        
        # Compile the generated C++ files with vcd_harness.cpp
        ${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cpp -I ../../backends/functional/cxx_runtime/ -I ../../backends/cxxrtl/runtime/ -o vcd_harness
        
        # Generate VCD files with base_name
        if ./vcd_harness ${base_name}_functional_cxx.vcd ${base_name}_cxxrtl.vcd ; then
            # Run vcdiff and capture the output
            output=$(vcdiff ${base_name}_functional_cxx.vcd ${base_name}_cxxrtl.vcd)

            # Check if there is any output
            if [ -n "$output" ]; then
                echo "Differences detected in $verilog_file:"
                echo "$output"
                failing_files["$verilog_file"]="Differences detected"
            else
                echo "No differences detected in $verilog_file."
            fi
        else
            echo "Failed to generate VCD files for $verilog_file."
            failing_files["$verilog_file"]="VCD generation failure"
        fi
    else
        echo "Yosys failed to process $verilog_file."
        failing_files["$verilog_file"]="Yosys failure"
    fi
done

# Check if the array of failing files is empty
if [ ${#failing_files[@]} -eq 0 ]; then
    echo "All files passed."
    exit 0
else
    echo "The following files failed:"
    for file in "${!failing_files[@]}"; do
        echo "$file: ${failing_files[$file]}"
    done
    exit 1
fi
