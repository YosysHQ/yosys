#!/bin/bash

set -e

OPTIND=1
seed=""    # default to no seed specified
abcopt=""
while getopts "A:S:" opt
do
    case "$opt" in
	A) abcopt="-A $OPTARG" ;;
	S) seed="-S $OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

bash ../tools/autotest.sh $abcopt $seed -G *.v

for f in `egrep -l 'expect-(wr-ports|rd-ports|rd-clk)' *.v`; do
	echo -n "Testing expectations for $f .."
	../../yosys -qp "proc; opt; memory -nomap;; dump -outfile ${f%.v}.dmp t:\$mem" $f
	if grep -q expect-wr-ports $f; then
		grep -q "parameter \\\\WR_PORTS $(gawk '/expect-wr-ports/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected number of write ports."; false; }
	fi
	if grep -q expect-rd-ports $f; then
		grep -q "parameter \\\\RD_PORTS $(gawk '/expect-rd-ports/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected number of read ports."; false; }
	fi
	if grep -q expect-rd-clk $f; then
		grep -q "connect \\\\RD_CLK \\$(gawk '/expect-rd-clk/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read clock."; false; }
	fi
	if grep -q expect-no-rd-clk $f; then
		grep -q "connect \\\\RD_CLK 1'x\$" ${f%.v}.dmp ||
				{ echo " ERROR: Expected no read clock."; false; }
	fi
	echo " ok."
done

