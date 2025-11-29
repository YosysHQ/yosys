#!/usr/bin/env bash

set -euo pipefail

! ../../yosys -p 'read_verilog alu_sub.v; proc; hierarchy -auto-top; sdc get_foo.sdc' 2>&1 | grep 'Unknown getter'
