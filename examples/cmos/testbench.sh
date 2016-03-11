#!/bin/bash

set -ex

../../yosys counter.ys
ngspice testbench.sp

