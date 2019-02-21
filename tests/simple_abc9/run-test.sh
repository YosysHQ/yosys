#!/bin/bash

OPTIND=1
seed=""    # default to no seed specified
while getopts "S:" opt
do
    case "$opt" in
	S) arg="${OPTARG#"${OPTARG%%[![:space:]]*}"}" # remove leading space
	   seed="SEED=$arg" ;;
    esac
done
shift "$((OPTIND-1))"

# check for Icarus Verilog
if ! which iverilog > /dev/null ; then
  echo "$0: Error: Icarus Verilog 'iverilog' not found."
  exit 1
fi

cp ../simple/*.v .
rm dff_different_styles.v # FIXME: dffsr1 fails because opt_rmdff does something fishy (#816)
rm partsel.v # FIXME: Contains 1'hx, thus write_xaiger fails
exec ${MAKE:-make} -f ../tools/autotest.mk $seed *.v EXTRA_FLAGS="-p \"hierarchy; synth -run coarse; techmap; opt -full; abc9 -lut 4\""
