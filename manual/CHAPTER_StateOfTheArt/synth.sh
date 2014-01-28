#!/bin/bash

yosys_bin="/usr/local/synthesis/src/yosys/yosys"
hana_bin="/usr/local/synthesis/src/hana/bin/hana"
vl2mv_bin="/usr/local/synthesis/bin/vl2mv"
vis_bin="/usr/local/synthesis/bin/vis"
iverilog_bin="/usr/local/synthesis/bin/iverilog-0.8"
odin_bin="/usr/local/synthesis/src/vtr_release/ODIN_II/odin_II.exe"
abc_bin="/usr/local/synthesis/src/alanmi-abc-b5750272659f/abc"
edif2ngd="/opt/Xilinx/14.3/ISE_DS/ISE/bin/lin64/edif2ngd"
netgen="/opt/Xilinx/14.3/ISE_DS/ISE/bin/lin64/netgen"

all_modes="yosys hana vis icarus odin"
all_sources="always01 always02 always03 arrays01 forgen01 forgen02"

if [ "$*" == "ALL" ]; then
	for mode in $all_modes; do
		for src in $all_sources; do
			echo "synth.sh $mode $src.v ${src}_${mode}.v"
			( set -x; bash synth.sh $mode $src.v ${src}_${mode}.v || rm -f ${src}_${mode}.v; ) > ${src}_${mode}.log 2>&1
		done
	done
	exit
fi

mode="$1"
source="$2"
output="$3"
prefix="${output%.v}"

help() {
	echo "$0 ALL" >&2
	echo "$0 {yosys|hana|vis|icarus|odin} <source-file> <output-file>" >&2
	exit 1
}

if [ "$#" != 3 -o ! -f "$source" ]; then
	help
fi

set -ex

case "$mode" in
	yosys)
		$yosys_bin -o $output -b "verilog -noattr" -p proc -p opt -p memory -p opt -p techmap -p opt $source ;;
	hana)
		$hana_bin -s $output $source ;;
	vis)
		$vl2mv_bin -o $prefix.mv $source
		{ echo "read_blif_mv $prefix.mv"; echo "write_verilog $output"; } | $abc_bin ;;
	icarus)
		rm -f $prefix.ngo $prefix.v
		$iverilog_bin -t fpga -o $prefix.edif $source
		$edif2ngd $prefix.edif $prefix.ngo
		$netgen -ofmt verilog $prefix.ngo $prefix.v
		sed -re '/timescale/ s,^,//,;' -i $prefix.v ;;
	odin)
		$odin_bin -o $prefix.blif -V $source
		sed -re 's,top\^,,g; s,clock,_clock,g;' -i $prefix.blif
		{ echo "read_blif $prefix.blif"; echo "write_verilog $output"; } | $abc_bin ;;
	*)
		help
esac

