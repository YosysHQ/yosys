#!/usr/bin/env bash

trap 'echo "ERROR in enable_exec.sh" >&2; exit 1' ERR

${YOSYS} -q -p 'exec -- echo should_not_run' 2>&1 | grep -F "The 'exec' command is disabled. Run Yosys with --enable-exec to enable it." > /dev/null

${YOSYS} -q -p '! echo should_not_run' 2>&1 | grep -F "shell escape ('!') is disabled" > /dev/null

${YOSYS} --enable-exec -p 'exec -- echo enabled_ok' 2>&1 | grep -F "enabled_ok" > /dev/null

${YOSYS} --enable-exec -p '! echo bang_ok' 2>&1 | grep -F "bang_ok" > /dev/null
