#!/usr/bin/env bash
set -eu
source ../gen-tests-makefile.sh
generate_mk --bash
exec ${MAKE:-make} -f run-test.mk
