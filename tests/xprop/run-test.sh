#!/usr/bin/env bash
set -e

python3 generate.py $@
${MAKE:-make} -f run-test.mk
