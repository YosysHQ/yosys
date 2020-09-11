#!/bin/bash
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys -ql ${x%.ys}.log $x
done
python3 frontend.py unix-socket frontend.sock
