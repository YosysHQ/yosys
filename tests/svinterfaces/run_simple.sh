#!/usr/bin/env bash

# Run a simple test with a .ys file

if [ $# != 1 ]; then
    echo >&2 "Expected 1 argument"
    exit 1
fi

echo -n "Test: $1 ->"
../../yosys $1.ys >$1.log_stdout 2>$1.log_stderr || {
    echo "ERROR!"
    exit 1
}
echo "ok"
