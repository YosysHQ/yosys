#!/usr/bin/env bash
set -e
for x in *.ys; do
	echo "Running $x.."
	../../yosys -ql ${x%.ys}.log $x
done
for s in *.sh; do
	if [ "$s" != "run-test.sh" ]; then
		echo "Running $s.."
		bash $s
	fi
done
