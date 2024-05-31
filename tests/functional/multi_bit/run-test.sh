#!/bin/bash

# Initialize an array to store the names of failing Verilog files and their failure types
declare -A failing_files

# Function to run the test on a given Verilog file
run_test() {
    # Define the common variable for the relative path
    BASE_PATH="../../../"

    local verilog_file=$1

    # Extract the base name without extension
    local base_name=$(basename "$verilog_file" .v)
    
    # Run yosys to process each Verilog file
    if ${BASE_PATH}yosys -p "read_verilog $verilog_file; write_functional_cxx my_module_functional_cxx.cc"; then
        echo "Yosys processed $verilog_file successfully."
        
        # Compile the generated C++ files with vcd_harness.cpp
        ${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cc -I ${BASE_PATH}backends/functional/cxx_runtime/ -o vcd_harness
        
        # Generate VCD files with base_name
        if ./vcd_harness ${base_name}_functional_cxx.vcd; then
	    
	    # Run yosys to process each Verilog file
	    if ${BASE_PATH}yosys -p "read_verilog $verilog_file; sim -r ${base_name}_functional_cxx.vcd -scope my_module -timescale 1us -sim-cmp"; then
		echo "Yosys sim $verilog_file successfully."
	    else
		echo "Yosys simulation of $verilog_file failed. There is a discrepancy with functional cxx"
		failing_files["$verilog_file"]="Yosys sim failure"
	    fi
	    
        else
            echo "Failed to generate VCD files for $verilog_file."
            failing_files["$verilog_file"]="VCD generation failure"
        fi
    else
        echo "Yosys failed to process $verilog_file."
        failing_files["$verilog_file"]="Yosys failure"
    fi
}

# Main function to run all tests
run_all_tests() {
    # Loop through all Verilog files in the verilog directory
    for verilog_file in verilog/*.v; do
        run_test "$verilog_file"
    done

    # Check if the array of failing files is empty
    if [ ${#failing_files[@]} -eq 0 ]; then
        echo "All files passed."
        return 0
    else
        echo "The following files failed:"
        for file in "${!failing_files[@]}"; do
            echo "$file: ${failing_files[$file]}"
        done
        return 1
    fi
}

# If the script is being sourced, do not execute the tests
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    run_all_tests
fi
