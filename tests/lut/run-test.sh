#!/bin/bash
set -e
for x in *.v; do
  echo "Running $x.."
  ../../yosys -q -s check_map.ys -l ${x%.v}.log $x
done

for x in map_cmp.v; do
  echo "Running $x.."
  ../../yosys -q -s check_map_lut6.ys -l ${x%.v}_lut6.log $x
done
