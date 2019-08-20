#!/bin/bash
set -e
for x in *.v; do
  echo "Running $x.."
  ../../yosys -q -s ${x%.v}.ys -l ./temp/${x%.v}.log $x
done
