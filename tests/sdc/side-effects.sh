#!/usr/bin/env bash

../../yosys -p 'read_verilog alu_sub.v; proc; hierarchy -auto-top; sdc side-effects.sdc' | grep 'This should print something:
YOSYS_SDC_MAGIC_NODE_0'
