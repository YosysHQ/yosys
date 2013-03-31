#!/bin/bash
set -ex
rm -rf verilog-sim-benchmarks
git clone http://git.veripool.org/git/verilog-sim-benchmarks
cd verilog-sim-benchmarks
patch -p1 < ../changes.diff
