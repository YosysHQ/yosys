#!/usr/bin/env bash
set -eu
python3 gen_memories.py
source ../../../gen-tests-makefile.sh
run_tests --yosys-scripts --bash
