#!/bin/bash
exec ${MAKE:-make} -f ../tools/autotest.mk EXTRA_FLAGS="-l hana_vlib.v" test_*.v
