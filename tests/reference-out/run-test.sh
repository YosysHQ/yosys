#!/bin/bash
# This script loops over all verilog files in the current directory. Each one
# is read by the Yosys and then written back using specified backends. Then
# each backend output is compared with a reference output. 

set +e
YOSYS=../../yosys

# List of backends
BACKEND=( "verilog" "ilang" "json" )
EXT=( "v" "il" "json" )

# Loop over all verilog files in this folder
for INP_FILE in *.v; do

    BASE_NAME=$(basename ${INP_FILE})
    BASE_NAME=${BASE_NAME%.*}

    # Test each backend
    for i in "${!BACKEND[@]}"; do
        echo "Checking "${BACKEND[i]}" against "${INP_FILE}" ..."

        REF_FILE=${BASE_NAME}/${BASE_NAME%.*}.ref.${EXT[i]}
        OUT_FILE=${BASE_NAME}/${BASE_NAME%.*}.out.${EXT[i]}

        # Check if the reference file exists
        if [ ! -f "${REF_FILE}" ]; then
            echo "ERROR: Reference file "${REF_FILE}" not found!"
            exit -1
        fi

        # Generate output
        set -e
        ${YOSYS} -p "read_verilog ${INP_FILE}; write_${BACKEND[i]} ${OUT_FILE}" >${OUT_FILE}.out.log 2>${OUT_FILE}.err.log

        # Compare files
        set +e
        diff -q -I "Yosys" ${OUT_FILE} ${REF_FILE}

        # Fail if there is a difference
        if [ $? -ne 0 ]; then
            echo "ERROR: output and reference differ!"
            diff -y --color=auto ${OUT_FILE} ${REF_FILE}
            exit -1
        fi
    done
done

