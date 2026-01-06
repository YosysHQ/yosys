#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
generate_mk --yosys-scripts --prove-sv
