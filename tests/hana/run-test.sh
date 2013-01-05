#!/bin/bash
make -C ../.. || exit 1
exec bash ../tools/autotest.sh -l hana_vlib.v test_*.v
