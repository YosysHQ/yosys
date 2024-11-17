#!/usr/bin/env bash

trap 'echo "ERROR in logger_cmd_error.sh" >&2; exit 1' ERR

(../../yosys -v 3 -p '
hierarchy -top nonexistent
'
) 2>&1 | grep -F "ERROR: Module \`nonexistent' not found!" > /dev/null
