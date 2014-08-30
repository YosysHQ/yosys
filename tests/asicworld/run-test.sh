#!/bin/bash
exec ${MAKE:-make} -f ../tools/autotest.mk EXTRA_FLAGS="-e" *.v
