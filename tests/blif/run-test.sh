#!/usr/bin/env bash
source ../common-env.sh
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys --no-version -ql ${x%.ys}.log $x >/dev/null 2>&1
done

for x in *.blif; do
  diff $x.out $x.ok
done