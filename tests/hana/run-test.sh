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

exec ${MAKE:-make} -j $(nproc) -f ../tools/autotest.mk $seed EXTRA_FLAGS="-l hana_vlib.v -n 300 -e" test_*.v
