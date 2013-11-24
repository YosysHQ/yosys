#!/bin/bash

libs=""
genvcd=false
use_isim=false
use_modelsim=false
verbose=false
keeprunning=false
backend_opts="-noattr -noexpr"
kompare_xst=false
scriptfiles=""
toolsdir="$(cd $(dirname $0); pwd)"

if [ ! -f $toolsdir/cmp_tbdata -o $toolsdir/cmp_tbdata.c -nt $toolsdir/cmp_tbdata ]; then
	( set -ex;  gcc -Wall -o $toolsdir/cmp_tbdata $toolsdir/cmp_tbdata.c; ) || exit 1
fi

while getopts iml:wkvrxs: opt; do
	case "$opt" in
		i)
			use_isim=true ;;
		m)
			use_modelsim=true ;;
		l)
			libs="$libs $(cd $(dirname $OPTARG); pwd)/$(basename $OPTARG)";;
		w)
			genvcd=true ;;
		k)
			keeprunning=true ;;
		v)
			verbose=true ;;
		r)
			backend_opts="$backend_opts norename" ;;
		x)
			kompare_xst=true ;;
		s)
			[[ "$OPTARG" == /* ]] || OPTARG="$PWD/$OPTARG"
			scriptfiles="$scriptfiles $OPTARG" ;;
		*)
			echo "Usage: $0 [-i] [-w] [-k] [-v] [-r] [-x] [-l libs] [-s script] verilog-files\n" >&2
			exit 1
	esac
done

create_ref() {
	if $kompare_xst; then
		echo "verilog work $1" > $2.prj
		cat <<- EOT > $2.xst
			run
			-ifn $2.prj -ifmt mixed -ofn $2 -ofmt NGC -p xc6slx4-3-tqg144
			-top $( grep ^module $1 | sed -r 's,[^0-9A-Za-z_]+, ,g' | awk '{ print $2; exit; }'; )
			-opt_mode Speed -opt_level 1 -iobuf NO
		EOT
		(
			set +x
			prefix="$2"
			xilver=$( ls -v /opt/Xilinx/ | grep '^[0-9]' | tail -n1; )
			case "$( uname -m )" in
			x86_64)
				set --; . /opt/Xilinx/$xilver/ISE_DS/settings64.sh ;;
			*)
				set --; . /opt/Xilinx/$xilver/ISE_DS/settings32.sh ;;
			esac
			set -x
			xst -ifn $prefix.xst
			netgen -w -ofmt verilog $prefix.ngc $prefix
		)
	else
		cp "$1" "$2.v"
	fi
}

compile_and_run() {
	exe="$1"; output="$2"; shift 2
	if $use_modelsim; then
		altver=$( ls -v /opt/altera/ | grep '^[0-9]' | tail -n1; )
		/opt/altera/$altver/modelsim_ase/bin/vlib work
		/opt/altera/$altver/modelsim_ase/bin/vlog "$@"
		/opt/altera/$altver/modelsim_ase/bin/vsim -c -do 'run -all; exit;' testbench | grep '#OUT#' > "$output"
	elif $use_isim; then
		(
			set +x
			files=( "$@" )
			xilver=$( ls -v /opt/Xilinx/ | grep '^[0-9]' | tail -n1; )
			case "$( uname -m )" in
			x86_64)
				set --; . /opt/Xilinx/$xilver/ISE_DS/settings64.sh ;;
			*)
				set --; . /opt/Xilinx/$xilver/ISE_DS/settings32.sh ;;
			esac
			set -x
			vlogcomp "${files[@]}"
			if $kompare_xst; then
				fuse -o "$exe" -lib unisims_ver -top testbench -top glbl
			else
				fuse -o "$exe" -top testbench
			fi
			{ echo "run all"; echo "exit"; } > run-all.tcl
			PATH="$PATH:" "$exe" -tclbatch run-all.tcl > "$output"
		)
	else
		iverilog -s testbench -o "$exe" "$@"
		vvp -n "$exe" > "$output"
	fi
}

shift $((OPTIND - 1))

for fn
do
	bn=${fn%.v}
	if [ "$bn" == "$fn" ]; then
		echo "Invalid argument: $fn" >&2
		exit 1
	fi
	[[ "$bn" == *_tb ]] && continue
	echo -n "Test: $bn "

	rm -f ${bn}.{err,log}
	mkdir -p ${bn}.out
	rm -rf ${bn}.out/*

	body() {
		cd ${bn}.out
		cp ../$fn $fn
		if [ ! -f ../${bn}_tb.v ]; then
			"$toolsdir"/../../yosys -b autotest -o ${bn}_tb.v $fn
		else
			cp ../${bn}_tb.v ${bn}_tb.v
		fi
		if $genvcd; then sed -i 's,// \$dump,$dump,g' ${bn}_tb.v; fi
		create_ref $fn ${bn}_ref
		compile_and_run  ${bn}_tb_ref ${bn}_out_ref ${bn}_tb.v ${bn}_ref.v $libs
		if $genvcd; then mv testbench.vcd ${bn}_ref.vcd; fi

		test_count=0
		test_passes() {
			"$toolsdir"/../../yosys -b "verilog $backend_opts" "$@" -o ${bn}_syn${test_count}.v $fn $scriptfiles
			compile_and_run ${bn}_tb_syn${test_count} ${bn}_out_syn${test_count} \
					${bn}_tb.v ${bn}_syn${test_count}.v $libs \
					"$toolsdir"/../../techlibs/common/simlib.v \
					"$toolsdir"/../../techlibs/common/simcells.v
			if $genvcd; then mv testbench.vcd ${bn}_syn${test_count}.vcd; fi
			$toolsdir/cmp_tbdata ${bn}_out_ref ${bn}_out_syn${test_count}
			test_count=$(( test_count + 1 ))
		}

		if [ -n "$scriptfiles" ]; then
			test_passes
		else
			test_passes -p "hierarchy; proc; memory; opt; fsm; opt"
			test_passes -p "hierarchy; proc; memory; opt; fsm; opt; techmap; opt"
			# test_passes -p "hierarchy; proc; memory; opt; fsm; opt; techmap -opt; opt; abc; opt"
		fi
		touch ../${bn}.log
	}

	if $verbose; then
		echo ".."
		echo "Output written to console." > ${bn}.err
		( set -ex; body; )
	else
		( set -ex; body; ) > ${bn}.err 2>&1
	fi

	if [ -f ${bn}.log ]; then
		mv ${bn}.err ${bn}.log
		echo "-> ok"
	else echo "-> ERROR!"; $keeprunning || exit 1; fi
done

exit 0
