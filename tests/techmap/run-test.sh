#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
run_tests --yosys-scripts --bash --yosys-args "-e 'select out of bounds'"
