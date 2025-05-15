#!/usr/bin/env bash
set -e
for x in *.ys; do
  echo "Running $x.."
  ../../yosys -ql ${x%.ys}.log $x
done
for x in *.tcl; do
	echo "Running $x.."
	../../yosys -ql ${x%.tcl}.log -c $x
done
