#!/bin/bash
set -e
for x in *.v; do
  echo "Running $x.."
  ../../yosys -q -s check_map.ys -l ${x%.v}.log $x
done
