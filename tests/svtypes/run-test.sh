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
for x in *.sv; do
	if [ ! -f "${x%.sv}.ys"  ]; then
		echo "all:: check-$x"
		echo "check-$x:"
		echo "	@echo 'Checking $x..'"
		echo "	@../../yosys -ql ${x%.sv}.log -p \"prep -top top; sat -verify -prove-asserts\" $x"
	fi
done
} > run-test.mk
exec ${MAKE:-make} -f run-test.mk
