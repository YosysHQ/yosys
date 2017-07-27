#!/bin/bash

set -ex

prefix=${1%.sv}
test -f $prefix.sv

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

	if [ "$1" = "fail" ]; then
		echo "verific -sv ${prefix}_fail.sv"
	else
		echo "verific -sv $prefix.sv"
	fi

	if [ -f $prefix.vhd ]; then
		echo "verific -vhdl2008 $prefix.vhd"
	fi

	cat <<- EOT
		verific -import -extnets -all top
		prep -top top

		[files]
		$prefix.sv
	EOT

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

generate_sby pass > ${prefix}_pass.sby
generate_sby fail > ${prefix}_fail.sby

sby --yosys $PWD/../../yosys -f ${prefix}_pass.sby
sby --yosys $PWD/../../yosys -f ${prefix}_fail.sby

touch $prefix.ok

