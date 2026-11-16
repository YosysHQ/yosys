#!/usr/bin/env bash
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

# check vcd2fst is available
vcd2fst -h

pytest -v -m "not smt and not rkt" "$SCRIPT_DIR" "$@"
