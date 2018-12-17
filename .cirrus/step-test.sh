#!/usr/bin/env bash

set -e -x

make -j $(nproc) test
