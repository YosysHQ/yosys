#!/usr/bin/env bash
set -eu
python3 mem_gen.py
source ../../../gen-tests-makefile.sh
generate_mk --yosys-scripts --bash
