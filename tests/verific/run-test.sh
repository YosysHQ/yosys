#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
generate_mk --yosys-scripts --bash
echo "$(echo 'export ASAN_OPTIONS=halt_on_error=0'; cat run-test.mk)" > run-test.mk