#!/bin/sh

#
# Script to writing btor from verilog design
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

./yosys -p "
read_verilog $1; 
hierarchy -top $3; 
hierarchy -libdir $DIR; 
hierarchy -check; 
script btor.ys; 
write_btor $2;"

