#!/bin/bash
set -e

python3 generate.py $@
make -f run-test.mk
