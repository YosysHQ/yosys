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
    local base_name=$(basename "$rtlil_file" .il)

    # Run yosys to process each RTLIL file
    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; write_functional_smt2 ${base_name}.smt2"; then
        echo "Yosys processed $rtlil_file successfully."
	# Check that the smt file generated is valid
        # Execute the Python script to create a VCD file from the SMT2 file
	if z3 "${base_name}.smt2"; then
            echo "SMT file ${base_name}.smt2 is valid ."

            if python3 using_smtio.py "${base_name}.smt2"; then
		echo "Python script generated VCD file for $rtlil_file successfully."

		# Check if VCD file was generated successfully
		if [ -f "${base_name}.smt2.vcd" ]; then
                    echo "VCD file ${base_name}.vcd generated successfully by Python."

                    # Run yosys simulation to generate a reference VCD file
                    if ${BASE_PATH}yosys -p "read_rtlil $rtlil_file; sim -vcd ${base_name}_yosys.vcd -r ${base_name}.smt2.vcd -scope gold -timescale 1us"; then
			echo "Yosys simulation for $rtlil_file completed successfully."
			successful_files["$rtlil_file"]="Success"
                    else
			echo "Yosys simulation failed for $rtlil_file."
			failing_files["$rtlil_file"]="Yosys simulation failure"
                    fi
		else
		    
                    echo "Failed to generate VCD file (${base_name}.vcd) for $rtlil_file. "
                    failing_files["$rtlil_file"]="VCD generation failure"
		fi
            else
		echo "Failed to run Python script for $rtlil_file."
		failing_files["$rtlil_file"]="Python script failure"
	    fi
	else
	    echo "SMT file for $rtlil_file is invalid"
	    failing_files["$rtlil_file"]="Invalid SMT"
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
        for file in "${!failing_files[@]}"]; do
    echo "$file: ${failing_files[$file]}"
done
echo "The following files passed:"
for file in "${!successful_files[@]}"]; do
					 echo "$file"
				     done
				      return 1
				     fi
				      }

				       # If the script is being sourced, do not execute the tests
				       if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
					   run_all_tests
				       fi
