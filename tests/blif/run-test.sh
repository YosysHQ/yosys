#!/usr/bin/env bash
source ../common-env.sh
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys --no-version -ql ${x%.ys}.log $x
done

for x in *.blif; do
  diff $x.out $x.ok
done