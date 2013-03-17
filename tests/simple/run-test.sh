#!/bin/bash

# check for Icarus Verilog
if ! which iverilog > /dev/null ; then
  echo "$0: Error: Icarus Verilog 'iverilog' not found."
  exit 1
fi

make -C ../.. || exit 1
exec bash ../tools/autotest.sh *.v
