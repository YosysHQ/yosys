#!/bin/bash -eu

../../yosys initial_display.v | awk '/<<<BEGIN>>>/,/<<<END>>>/ {print $0}' >yosys-initial_display.log
iverilog -o iverilog-initial_display initial_display.v
./iverilog-initial_display >iverilog-initial_display.log
diff yosys-initial_display.log iverilog-initial_display.log
