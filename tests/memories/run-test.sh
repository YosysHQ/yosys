#!/bin/bash

set -e

OPTIND=1
seed=""    # default to no seed specified
while getopts "S:" opt
do
    case "$opt" in
	S) seed="-S $OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

bash ../tools/autotest.sh $seed -G *.v

for f in `egrep -l 'expect-(wr|rd)-ports' *.v`; do
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
	echo " ok."
done

