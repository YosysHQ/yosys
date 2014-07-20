#!/bin/bash

set -e
mkdir -p log_test_share
source common.sh

f=$1
n=$(basename ${f%.v})

rm -f log_test_share/$n.txt
rm -f log_test_share/$n.err

if ! ../../yosys -q -l log_test_share/$n.out - 2> /dev/null <<- EOT
	read_verilog $f
	proc;;

	copy $n gold
	rename $n work

	cd work
	share -aggressive
	cd ..

	miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold work miter
	sat -set-def-inputs -verify -prove trigger 0 -show-inputs -show-outputs miter
EOT
then
	log_fail test_share $n
	mv log_test_share/$n.out log_test_share/$n.err
	exit 1
fi

log_pass test_share $n
mv log_test_share/$n.out log_test_share/$n.txt
exit 0

