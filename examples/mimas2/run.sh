#!/bin/sh
set -e
yosys run_yosys.ys
edif2ngd example.edif
ngdbuild example -uc example.ucf -p xc6slx9csg324-3
map -w example
par -w example.ncd example_par.ncd
bitgen -w example_par.ncd -g StartupClk:JTAGClk
