#!/bin/bash
make -C ../.. || exit 1
exec bash ../tools/autotest.sh *.v
