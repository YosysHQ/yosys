#!/bin/bash
set -ex
yosys demo.ys
$TD_HOME/bin/td build.tcl
