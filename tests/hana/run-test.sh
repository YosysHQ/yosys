#!/bin/bash
exec ${MAKE:-make} -f ../tools/autotest.mk EXTRA_FLAGS="-l hana_vlib.v -n 300 -e" test_*.v
