#!/bin/bash
yosys run_yosys.ys
vivado -nolog -nojournal -mode batch -source run_vivado.tcl
vivado -nolog -nojournal -mode batch -source run_prog.tcl
