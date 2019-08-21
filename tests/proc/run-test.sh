#!/bin/bash
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys -ql ${x%.ys}.log $x
done
