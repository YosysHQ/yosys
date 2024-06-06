#!/bin/bash

# Initialize an array to store the names of failing RTLIL files and their failure types
declare -A failing_files
# Initialize an array to store the names of successful RTLIL files
declare -A successful_files

# Function to run the test on a given RTLIL file
run_test() {
    # Define the common variable for the relative path
    BASE_PATH="../../../"

    local rtlil_file=$1

    # Extract the base name without extension
    local base_name=$(basename "$rtlil_file" .v)
    
    # Run yosys to process each RTLIL file
    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; write_functional_cxx my_module_functional_cxx.cc"; then
        echo "Yosys processed $rtlil_file successfully."
        
        # Compile the generated C++ files with vcd_harness.cpp
        if ${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cc -I ${BASE_PATH}backends/functional/cxx_runtime/ -std=c++17 -o vcd_harness; then
            echo "Compilation successful."
            # Generate VCD files with base_name
            if ./vcd_harness ${base_name}_functional_cxx.vcd; then
		
		# Run yosys to process each RTLIL file
		if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -r ${base_name}_functional_cxx.vcd -scope gold -vcd ${base_name}_yosys_sim.vcd -timescale 1us -sim-gold"; then
		    echo "Yosys sim $rtlil_file successfully."
		    successful_files["$rtlil_file"]="Success"
		else
		    ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -vcd ${base_name}_yosys_sim.vcd -r ${base_name}_functional_cxx.vcd -scope gold -timescale 1us"
		    echo "Yosys simulation of $rtlil_file failed. There is a discrepancy with functional cxx"
		    failing_files["$rtlil_file"]="Yosys sim failure"
		fi
		
            else
		echo "Failed to generate VCD files for $rtlil_file."
		failing_files["$rtlil_file"]="VCD generation failure"
            fi
	else
	    echo "Failed to compile harness for $rtlil_file."
	    failing_files["$rtlil_file"]="Compilation failure"
	fi
	else
            echo "Yosys failed to process $rtlil_file."
            failing_files["$rtlil_file"]="Yosys failure"
	fi
}

# Main function to run all tests
run_all_tests() {
    # Loop through all RTLIL files in the rtlil directory
    for rtlil_file in rtlil/*.il; do
        run_test "$rtlil_file"
    done

    # Check if the array of failing files is empty
    if [ ${#failing_files[@]} -eq 0 ]; then
        echo "All files passed."
	echo "The following files passed:"
        for file in "${!successful_files[@]}"; do
            echo "$file"
        done
        return 0
    else
        echo "The following files failed:"
        for file in "${!failing_files[@]}"; do
            echo "$file: ${failing_files[$file]}"
        done
	echo "The following files passed:"
        for file in "${!successful_files[@]}"; do
            echo "$file"
        done
        return 1
    fi
}

# If the script is being sourced, do not execute the tests
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    run_all_tests
fi
