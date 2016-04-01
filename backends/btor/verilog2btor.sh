#!/bin/sh

#
# Script to write BTOR from Verilog design
#

if [ "$#" -ne 3 ]; then
  echo "Usage: $0 input.v output.btor top-module-name" >&2
  exit 1
fi
if ! [ -e "$1" ]; then
  echo "$1 not found" >&2
  exit 1
fi

FULL_PATH=$(readlink -f $1)
DIR=$(dirname $FULL_PATH)

./yosys -q -p "
read_verilog -sv $1;
hierarchy -top $3;
hierarchy -libdir $DIR;
hierarchy -check;
proc;
opt; opt_expr -mux_undef; opt;
rename -hide;;;
#techmap -map +/pmux2mux.v;;
splice; opt;
memory_dff -wr_only;
memory_collect;;
flatten;;
memory_unpack;
splitnets -driver;
setundef -zero -undriven;
opt;;;
write_btor $2;"

