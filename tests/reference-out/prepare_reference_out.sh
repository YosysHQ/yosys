#!/bin/bash
# This script generates reference outpus for testing.
# Usage: prepare_reference_out.sh <verilog_file_name>

INP_FILE=$1

BASE_NAME=$(basename ${INP_FILE})
BASE_NAME=${BASE_NAME%.*}

mkdir -p ${BASE_NAME}

# List of backends
BACKEND=( "verilog" "ilang" "json" )
EXT=( "v" "il" "json" )

set -e

# Generate
for i in "${!BACKEND[@]}"; do
    REF_FILE=${BASE_NAME}/${BASE_NAME%.*}.ref.${EXT[i]}    
    ${YOSYS} -p "read_verilog $1; write_${BACKEND[i]} ${REF_FILE}" >${REF_FILE}.out.log 2>${REF_FILE}.err.log
done

