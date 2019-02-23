#!/usr/bin/env bash
set -e
for x in *.ys; do
	echo "Running $x.."
	../../yosys -ql ${x%.ys}.log $x
done
# Run any .sh files in this directory (with the exception of the file - run-test.sh
shell_tests=$(echo *.sh | sed -e 's/run-test.sh//')
if [ "$shell_tests" ]; then
    for s in $shell_tests; do
        echo "Running $s.."
        bash $s
    done
fi
