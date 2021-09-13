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
if ! command -v iverilog > /dev/null ; then
  echo "$0: Error: Icarus Verilog 'iverilog' not found."
  exit 1
fi

for file in `ls *.v *.sv`; do
    if [ ! -f "../simple/$file" -a "$file" != "abc9.v" ]; then
	echo "Warning: $file is in simple_abc9/, but not in simple/"
	backup="$file.bak"
	if [ -f "$backup" ]; then
	    if cmp "$file" "$backup" > /dev/null; then
		echo " => $backup already exists and matches; removing $file"
		rm "$file"
	    else
		echo " => $backup already exists but differs; leaving $file in place"
	    fi
	else
	    echo " => moving $file to $backup"
	    mv -i "$file" "$backup"
	fi
    fi
done

cp ../simple/*.v .
cp ../simple/*.sv .
rm specify.v # bug 2675
DOLLAR='?'
exec ${MAKE:-make} -f ../tools/autotest.mk $seed *.v *.sv EXTRA_FLAGS="-f \"verilog -noblackbox -specify\" -n 300 -p '\
    read_verilog -icells -lib +/abc9_model.v; \
    hierarchy; \
    synth -run coarse; \
    opt -full; \
    techmap; \
    abc9 -lut 4; \
    clean; \
    check -assert * abc9_test037 %d; \
    select -assert-none t:${DOLLAR}_NOT_ t:${DOLLAR}_AND_ %%; \
    setattr -mod -unset blackbox -unset whitebox'"

# NOTE: Skip 'check -assert' on abc9_test037 because it intentionally has a combinatorial loop
