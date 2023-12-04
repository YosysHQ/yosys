#!/usr/bin/env bash
set -eu
python3 mem_gen.py
source ../../../gen-tests-makefile.sh
run_tests --yosys-scripts --bash
