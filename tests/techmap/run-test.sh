#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
generate_mk --yosys-scripts --tcl-scripts --bash --yosys-args "-e 'select out of bounds'"
