#!/usr/bin/env bash

set -e -x

ncpu=4
if nproc; then
    ncpu=$(nproc)
fi

make -j ${ncpu} test
