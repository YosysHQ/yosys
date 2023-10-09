#!/usr/bin/env bash
set -eu
source ../../../gen-tests-makefile.sh
run_tests --yosys-scripts --bash --yosys-args "-w 'Yosys has only limited support for tri-state logic at the moment.'"
