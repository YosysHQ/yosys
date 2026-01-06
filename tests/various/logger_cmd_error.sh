#!/usr/bin/env bash

trap 'echo "ERROR in logger_cmd_error.sh" >&2; exit 1' ERR

(../../yosys -v 3 -C <<EOF
yosys -import
hierarchy -top nonexistent
EOF
) 2>&1 | grep -F "ERROR: Module \`nonexistent' not found!" > /dev/null
