#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
generate_mk --yosys-scripts --bash
sed -i '1i\export ASAN_OPTIONS=halt_on_error=0' run-test.mk
