#!/bin/bash
exec ${MAKE:-make} -f ../tools/autotest.mk *.v
