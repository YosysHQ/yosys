#!/bin/sh

set -e
DIR=$(dirname "$0")
ROOT=$(realpath "$DIR/../../..")
YOSYS="$ROOT/build-rel/yosys"

test() {
	echo "Running: $YOSYS -q -p \"read_verilog $1; equiv_opt -assert mcm; design -load postopt; select -assert-count 0 t:\$mul\""
	$YOSYS -q -p "read_verilog $1; equiv_opt -assert mcm; design -load postopt; select -assert-count 0 t:\$mul"
}

# This runs forever, don't bother with until fixed
for file in $DIR/verilog/*.v; do
	test "$file"
done
