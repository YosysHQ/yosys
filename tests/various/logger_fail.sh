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
	output=`../../yosys -q "$@" 2>&1`
	if [ $? -ne 1 ]; then
		fail "exit code for '$desc' was not 1"
	fi
	if [ "$output" != "$want" ]; then
		fail "output for '$desc' did not match"
	fi
}

unmet() {
	kind=$1
	runTest "unmet $kind" \
		"ERROR: Expected $kind pattern 'foobar' not found !" \
		-p "logger -expect $kind \"foobar\" 1"
}

unmet log
unmet warning
unmet error

runTest "too many logs" \
	"ERROR: Expected log pattern 'statistics' found 2 time(s), instead of 1 time(s) !" \
	-p "logger -expect log \"statistics\" 1" -p stat -p stat

runTest "too many warnings" \
	"Warning: Found log message matching -W regex:
Printing statistics.
ERROR: Expected warning pattern 'statistics' found 2 time(s), instead of 1 time(s) !" \
	-p "logger -warn \"Printing statistics\"" \
	-p "logger -expect warning \"statistics\" 1" -p stat -p stat
