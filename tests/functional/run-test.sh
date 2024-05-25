#!/bin/bash

set -ex

../../yosys -p "read_verilog verilog/and.v; write_cxxrtl and_cxxrtl.cc; write_functional_cxx and_functional_cxx.cc"
${CXX:-g++} -g -fprofile-arcs -ftest-coverage vcd_harness.cpp -I ../../backends/functional/cxx_runtime/ -I ../../backends/cxxrtl/runtime/ -o vcd_harness
./vcd_harness
