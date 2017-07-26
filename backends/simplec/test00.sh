#!/bin/bash
set -ex
../../yosys -p 'synth -top test; write_simplec -verbose -i8 test00_uut.c' test00_uut.v
clang -o test00_tb test00_tb.c
./test00_tb
