#!/usr/bin/env bash
source ../common-env.sh
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys -ql ${x%.ys}.log $x
done
