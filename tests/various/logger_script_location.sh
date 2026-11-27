#!/usr/bin/env bash

fail() {
	echo "$1" >&2
	exit 1
}

runTest() {
	desc="$1"
	want="$2"
	shift 2
	echo "running '$desc' with args $@"
	output=`${YOSYS} -q "$@" 2>&1`
	if [ $? -ne 1 ]; then
		fail "exit code for '$desc' was not 1"
	fi
	if [ "$output" != "$want" ]; then
		fail "output for '$desc' did not match"
	fi
}

command_error="ERROR: Module \`missing_top' not found!"
script_error="script_location/error.ys:6: $command_error"
runTest "script flag" "$script_error" -s script_location/error.ys
runTest "script frontend" "$script_error" script_location/error.ys

tcl_error="$command_error
script_location/error.tcl:2: ERROR: TCL interpreter returned an error: Yosys command produced an error"
runTest "tcl flag" \
	"$tcl_error" \
	-c script_location/error.tcl

runTest "tcl pass" \
	"$tcl_error" \
	-p 'tcl script_location/error.tcl'

runTest "tcl from script" \
	"$tcl_error" \
	-s script_location/tcl.ys
