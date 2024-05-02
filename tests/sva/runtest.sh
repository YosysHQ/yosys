#!/usr/bin/env bash

set -e

prefix=${1%.ok}
prefix=${prefix%.sv}
prefix=${prefix%.vhd}
test -f $prefix.sv -o -f $prefix.vhd

generate_sby() {
	cat <<- EOT
		[options]
		mode bmc
		depth 10
		expect $1

		[engines]
		smtbmc yices

		[script]
	EOT

	if [ -f $prefix.sv ]; then
		if [ "$1" = "fail" ]; then
			echo "read -sv ${prefix}_fail.sv"
		else
			echo "read -sv $prefix.sv"
		fi
	fi

	if [ -f $prefix.vhd ]; then
		echo "read -vhdl $prefix.vhd"
	fi

	cat <<- EOT
		prep -top top
		chformal -early -assume

		[files]
	EOT

	if [ -f $prefix.sv ]; then
		echo "$prefix.sv"
	fi

	if [ -f $prefix.vhd ]; then
		echo "$prefix.vhd"
	fi

	if [ "$1" = "fail" ]; then
		cat <<- EOT

			[file ${prefix}_fail.sv]
			\`define FAIL
			\`include "$prefix.sv"
		EOT
	fi
}

if [ -f $prefix.ys ]; then
	set -x
	$PWD/../../yosys -q -e "Assert .* failed." -s $prefix.ys
elif [ -f $prefix.sv ]; then
	generate_sby pass > ${prefix}_pass.sby
	generate_sby fail > ${prefix}_fail.sby

	# Check that SBY is up to date enough for this yosys version
	if sby --help | grep -q -e '--status'; then
		set -x
		sby --yosys $PWD/../../yosys -f ${prefix}_pass.sby
		sby --yosys $PWD/../../yosys -f ${prefix}_fail.sby
	else
		echo "sva test '${prefix}' requires an up to date SBY, skipping"
	fi
else
	generate_sby pass > ${prefix}.sby

	# Check that SBY is up to date enough for this yosys version
	if sby --help | grep -q -e '--status'; then
		set -x
		sby --yosys $PWD/../../yosys -f ${prefix}.sby
	else
		echo "sva test '${prefix}' requires an up to date SBY, skipping"
	fi
fi

{ set +x; } &>/dev/null

touch $prefix.ok

