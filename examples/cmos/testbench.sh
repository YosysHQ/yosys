#!/bin/bash

set -ex

../../yosys counter.ys
ngspice testbench.sp

# requires ngspice with xspice support enabled:
#ngspice testbench_digital.sp

