#!/bin/bash

set -ex

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
			echo "verific -sv ${prefix}_fail.sv"
		else
			echo "verific -sv $prefix.sv"
		fi
	fi

	if [ -f $prefix.vhd ]; then
		echo "verific -vhdl $prefix.vhd"
	fi

	cat <<- EOT
		verific -import -extnets -all top
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

if [ -f $prefix.sv ]; then
	generate_sby pass > ${prefix}_pass.sby
	generate_sby fail > ${prefix}_fail.sby
	sby --yosys $PWD/../../yosys -f ${prefix}_pass.sby
	sby --yosys $PWD/../../yosys -f ${prefix}_fail.sby
else
	generate_sby pass > ${prefix}.sby
	sby --yosys $PWD/../../yosys -f ${prefix}.sby
fi

touch $prefix.ok

