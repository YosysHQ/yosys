#!/usr/bin/env bash
set -eu
python3 generate.py
source ../../../gen-tests-makefile.sh
run_tests --yosys-scripts --bash
