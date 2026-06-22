#!/usr/bin/env bash

set -ex

../../yosys counter.ys
ngspice testbench.sp

