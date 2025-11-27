#!/usr/bin/env bash
source ../common-env.sh
set -e

python3 generate.py $@
${MAKE:-make} -f run-test.mk
