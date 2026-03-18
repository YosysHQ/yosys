#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate_autotest("*.v", "",
"""if grep -Eq 'expect-(wr-ports|rd-ports|rd-clk)' $@; then \\
	$(YOSYS) -f verilog -qp "proc; opt; memory -nomap; dump -outfile $(@:.v=).dmp t:\\$$mem_v2" $@; \\
	if grep -q expect-wr-ports $@; then \\
		val=$$(gawk '/expect-wr-ports/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\WR_PORTS $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected number of write ports."; exit 1; }; \\
	fi; \\
	if grep -q expect-wr-wide-continuation $@; then \\
		val=$$(gawk '/expect-wr-wide-continuation/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\WR_WIDE_CONTINUATION $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected write wide continuation."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-ports $@; then \\
		val=$$(gawk '/expect-rd-ports/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\RD_PORTS $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected number of read ports."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-clk $@; then \\
		val=$$(gawk '/expect-rd-clk/ { print $$3; }' $@); \\
		grep -Fq "connect \\\\RD_CLK $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read clock."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-en $@; then \\
		val=$$(gawk '/expect-rd-en/ { print $$3; }' $@); \\
		grep -Fq "connect \\\\RD_EN $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read enable."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-srst-sig $@; then \\
		val=$$(gawk '/expect-rd-srst-sig/ { print $$3; }' $@); \\
		grep -Fq "connect \\\\RD_SRST $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read sync reset."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-srst-val $@; then \\
		val=$$(gawk '/expect-rd-srst-val/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\RD_SRST_VALUE $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read sync reset value."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-arst-sig $@; then \\
		val=$$(gawk '/expect-rd-arst-sig/ { print $$3; }' $@); \\
		grep -Fq "connect \\\\RD_ARST $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read async reset."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-arst-val $@; then \\
		val=$$(gawk '/expect-rd-arst-val/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\RD_ARST_VALUE $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read async reset value."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-init-val $@; then \\
		val=$$(gawk '/expect-rd-init-val/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\RD_INIT_VALUE $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read init value."; exit 1; }; \\
	fi; \\
	if grep -q expect-rd-wide-continuation $@; then \\
		val=$$(gawk '/expect-rd-wide-continuation/ { print $$3; }' $@); \\
		grep -Fq "parameter \\\\RD_WIDE_CONTINUATION $$val" $(@:.v=).dmp || { echo " ERROR: Unexpected read wide continuation."; exit 1; }; \\
	fi; \\
	if grep -q expect-no-rd-clk $@; then \\
		grep -Fq "connect \\\\RD_CLK 1'x" $(@:.v=).dmp || { echo " ERROR: Expected no read clock."; exit 1; }; \\
	fi; \\
fi""")