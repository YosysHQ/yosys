#!/usr/bin/env bash
set -eu

OPTIND=1
seed=""    # default to no seed specified
while getopts "S:" opt
do
    case "$opt" in
	S) seed="$OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

python3 generate.py
exec ${MAKE:-make} -f run-test.mk SEED="$seed"
