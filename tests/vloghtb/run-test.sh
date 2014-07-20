#!/bin/bash

set -ex

rm -rf Makefile refdat rtl scripts spec vloghammer_tb.tar.bz2
wget http://www.clifford.at/yosys/nogit/vloghammer_tb.tar.bz2
tar --strip=1 -xjf vloghammer_tb.tar.bz2

make clean
make -j4 EXIT_ON_ERROR=1 YOSYS_BIN=$PWD/../../yosys YOSYS_SCRIPT="proc;;" check_yosys

rm -rf log_test_*
make -j4 -f test_makefile MODE=share

