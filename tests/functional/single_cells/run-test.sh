#!/bin/bash

declare -A cxx_failing_files
declare -A smt_failing_files
declare -A cxx_successful_files
declare -A smt_successful_files

run_cxx_test() {
    BASE_PATH="../../../"

    local rtlil_file=$1

    local base_name=$(basename "$rtlil_file" .v)
    
    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; write_functional_cxx my_module_functional_cxx.cc"; then
        echo "Yosys processed $rtlil_file successfully."
        
        if ${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cc -I ${BASE_PATH}backends/functional/cxx_runtime/ -std=c++17 -o vcd_harness; then
            echo "Compilation successful."
            if ./vcd_harness ${base_name}_functional_cxx.vcd; then
		
		if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -r ${base_name}_functional_cxx.vcd -scope gold -vcd ${base_name}_yosys_sim.vcd -timescale 1us -sim-gold"; then
		    echo "Yosys sim $rtlil_file successfully."
		    cxx_successful_files["$rtlil_file"]="Success"
		else
		    ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -vcd ${base_name}_yosys_sim.vcd -r ${base_name}_functional_cxx.vcd -scope gold -timescale 1us"
		    echo "Yosys simulation of $rtlil_file failed. There is a discrepancy with functional cxx"
		    cxx_failing_files["$rtlil_file"]="Yosys sim failure"
		fi
		
            else
		echo "Failed to generate VCD files for $rtlil_file."
		cxx_failing_files["$rtlil_file"]="VCD generation failure"
            fi
	else
	    echo "Failed to compile harness for $rtlil_file."
	    cxx_failing_files["$rtlil_file"]="Compilation failure"
	fi
	else
            echo "Yosys failed to process $rtlil_file."
            cxx_failing_files["$rtlil_file"]="Yosys failure"
	fi
}

run_smt_test() {
    BASE_PATH="../../../"

    local rtlil_file=$1

    local base_name=$(basename "$rtlil_file" .il)

    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; write_functional_smt2 ${base_name}.smt2"; then
        echo "Yosys processed $rtlil_file successfully."
	# TODO: which SMT solver should be run?
	if z3 "${base_name}.smt2"; then
            echo "SMT file ${base_name}.smt2 is valid ."

            if python3 using_smtio.py "${base_name}.smt2"; then
		echo "Python script generated VCD file for $rtlil_file successfully."

		if [ -f "${base_name}.smt2.vcd" ]; then
                    echo "VCD file ${base_name}.vcd generated successfully by Python."

                    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -vcd ${base_name}_yosys.vcd -r ${base_name}.smt2.vcd -scope gold -timescale 1us"; then
			echo "Yosys simulation for $rtlil_file completed successfully."
			smt_successful_files["$rtlil_file"]="Success"
                    else
			echo "Yosys simulation failed for $rtlil_file."
			smt_failing_files["$rtlil_file"]="Yosys simulation failure"
                    fi
		else
		    
                    echo "Failed to generate VCD file (${base_name}.vcd) for $rtlil_file. "
                    smt_failing_files["$rtlil_file"]="VCD generation failure"
		fi
            else
		echo "Failed to run Python script for $rtlil_file."
		smt_failing_files["$rtlil_file"]="Python script failure"
	    fi
	else
	    echo "SMT file for $rtlil_file is invalid"
	    smt_failing_files["$rtlil_file"]="Invalid SMT"
	fi
    else
        echo "Yosys failed to process $rtlil_file."
        smt_failing_files["$rtlil_file"]="Yosys failure"
    fi
}


run_all_tests() {
    return_code=0
    for rtlil_file in rtlil/*.il; do
        run_cxx_test "$rtlil_file"
	run_smt_test "$rtlil_file"
    done
    
    echo "C++ tests results:"
    if [ ${#cxx_failing_files[@]} -eq 0 ]; then
        echo "All files passed."
	echo "The following files passed:"
        for file in "${!cxx_successful_files[@]}"; do
            echo "$file"
        done
    else
        echo "The following files failed:"
        for file in "${!cxx_failing_files[@]}"; do
            echo "$file: ${cxx_failing_files[$file]}"
        done
	echo "The following files passed:"
        for file in "${!cxx_successful_files[@]}"; do
            echo "$file"
        done
	return_code=1
    fi
    
    echo "SMT tests results:"
    if [ ${#smt_failing_files[@]} -eq 0 ]; then
        echo "All files passed."
	echo "The following files passed:"
        for file in "${!smt_successful_files[@]}"; do
            echo "$file"
        done
    else
        echo "The following files failed:"
        for file in "${!smt_failing_files[@]}"; do
            echo "$file: ${smt_failing_files[$file]}"
        done
	echo "The following files passed:"
        for file in "${!smt_successful_files[@]}"; do
            echo "$file"
        done
	return_code=1
    fi
    return $return_code
}

# If the script is being sourced, do not execute the tests
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    run_all_tests
fi
