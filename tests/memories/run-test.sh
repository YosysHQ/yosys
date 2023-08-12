#!/usr/bin/env bash

set -e

OPTIND=1
seed=""    # default to no seed specified
abcopt=""
while getopts "A:S:" opt
do
    case "$opt" in
	A) abcopt="-A $OPTARG" ;;
	S) seed="$OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

${MAKE:-make} -f ../tools/autotest.mk SEED="$seed" EXTRA_FLAGS="$abcopt" *.v

for f in `egrep -l 'expect-(wr-ports|rd-ports|rd-clk)' *.v`; do
	echo -n "Testing expectations for $f .."
	../../yosys -f verilog -qp "proc; opt; memory -nomap;; dump -outfile ${f%.v}.dmp t:\$mem_v2" $f
	if grep -q expect-wr-ports $f; then
		grep -q "parameter \\\\WR_PORTS $(gawk '/expect-wr-ports/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected number of write ports."; false; }
	fi
	if grep -q expect-wr-wide-continuation $f; then
		grep -q "parameter \\\\WR_WIDE_CONTINUATION $(gawk '/expect-wr-wide-continuation/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected write wide continuation."; false; }
	fi
	if grep -q expect-rd-ports $f; then
		grep -q "parameter \\\\RD_PORTS $(gawk '/expect-rd-ports/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected number of read ports."; false; }
	fi
	if grep -q expect-rd-clk $f; then
		grep -q "connect \\\\RD_CLK \\$(gawk '/expect-rd-clk/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read clock."; false; }
	fi
	if grep -q expect-rd-en $f; then
		grep -q "connect \\\\RD_EN \\$(gawk '/expect-rd-en/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read enable."; false; }
	fi
	if grep -q expect-rd-srst-sig $f; then
		grep -q "connect \\\\RD_SRST \\$(gawk '/expect-rd-srst-sig/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read sync reset."; false; }
	fi
	if grep -q expect-rd-srst-val $f; then
		grep -q "parameter \\\\RD_SRST_VALUE $(gawk '/expect-rd-srst-val/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read sync reset value."; false; }
	fi
	if grep -q expect-rd-arst-sig $f; then
		grep -q "connect \\\\RD_ARST \\$(gawk '/expect-rd-arst-sig/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read async reset."; false; }
	fi
	if grep -q expect-rd-arst-val $f; then
		grep -q "parameter \\\\RD_ARST_VALUE $(gawk '/expect-rd-arst-val/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read async reset value."; false; }
	fi
	if grep -q expect-rd-init-val $f; then
		grep -q "parameter \\\\RD_INIT_VALUE $(gawk '/expect-rd-init-val/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read init value."; false; }
	fi
	if grep -q expect-rd-wide-continuation $f; then
		grep -q "parameter \\\\RD_WIDE_CONTINUATION $(gawk '/expect-rd-wide-continuation/ { print $3; }' $f)\$" ${f%.v}.dmp ||
				{ echo " ERROR: Unexpected read wide continuation."; false; }
	fi
	if grep -q expect-no-rd-clk $f; then
		grep -q "connect \\\\RD_CLK 1'x\$" ${f%.v}.dmp ||
				{ echo " ERROR: Expected no read clock."; false; }
	fi
	echo " ok."
done

