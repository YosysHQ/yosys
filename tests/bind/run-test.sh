#!/usr/bin/env bash
set -e
{
echo "all::"
for x in *.ys; do
	echo "all:: run-$x"
	echo "run-$x:"
	echo "	@echo 'Running $x..'"
	echo "	@../../yosys -ql ${x%.ys}.log $x"
done
for s in *.sh; do
	if [ "$s" != "run-test.sh" ]; then
		echo "all:: run-$s"
		echo "run-$s:"
		echo "	@echo 'Running $s..'"
		echo "	@bash $s"
	fi
done
} > run-test.mk
exec ${MAKE:-make} -f run-test.mk
