#!/usr/bin/env bash

libs=""
genvcd=false
use_xsim=false
use_modelsim=false
verbose=false
keeprunning=false
makejmode=false
frontend="verilog -noblackbox"
backend_opts="-noattr -noexpr -siminit"
autotb_opts=""
include_opts=""
xinclude_opts=""
minclude_opts=""
scriptfiles=""
scriptopt=""
toolsdir="$(cd $(dirname $0); pwd)"
warn_iverilog_git=false
# The following are used in verilog to firrtl regression tests.
# Typically these will be passed as environment variables:
#EXTRA_FLAGS="--firrtl2verilog 'java -cp /.../firrtl/utils/bin/firrtl.jar firrtl.Driver'"
# The tests are skipped if firrtl2verilog is the empty string (the default).
firrtl2verilog=""
xfirrtl="../xfirrtl"
abcprog="$toolsdir/../../yosys-abc"

if [ ! -f $toolsdir/cmp_tbdata -o $toolsdir/cmp_tbdata.c -nt $toolsdir/cmp_tbdata ]; then
	( set -ex; ${CC:-gcc} -Wall -o $toolsdir/cmp_tbdata $toolsdir/cmp_tbdata.c; ) || exit 1
fi

while getopts xmGl:wkjvref:s:p:n:S:I:A:-: opt; do
	case "$opt" in
		x)
			use_xsim=true ;;
		m)
			use_modelsim=true ;;
		G)
			warn_iverilog_git=true ;;
		l)
			libs="$libs $(cd $(dirname $OPTARG); pwd)/$(basename $OPTARG)";;
		w)
			genvcd=true ;;
		k)
			keeprunning=true ;;
		j)
			makejmode=true ;;
		v)
			verbose=true ;;
		r)
			backend_opts="$backend_opts -norename" ;;
		e)
			backend_opts="$( echo " $backend_opts " | sed 's, -noexpr , ,; s,^ ,,; s, $,,;'; )" ;;
		f)
			frontend="$OPTARG" ;;
		s)
			[[ "$OPTARG" == /* ]] || OPTARG="$PWD/$OPTARG"
			scriptfiles="$scriptfiles $OPTARG" ;;
		p)
			scriptopt="$OPTARG" ;;
		n)
			autotb_opts="$autotb_opts -n $OPTARG" ;;
		S)
			autotb_opts="$autotb_opts -seed $OPTARG" ;;
		I)
			include_opts="$include_opts -I $OPTARG"
			xinclude_opts="$xinclude_opts -i $OPTARG"
			minclude_opts="$minclude_opts +incdir+$OPTARG" ;;
		A)
			abcprog="$OPTARG" ;;
		-)
			case "${OPTARG}" in
			    xfirrtl)
			    	xfirrtl="${!OPTIND}"
				OPTIND=$(( $OPTIND + 1 ))
				;;
			    firrtl2verilog)
			    	firrtl2verilog="${!OPTIND}"
				OPTIND=$(( $OPTIND + 1 ))
				;;
			    *)
			    	if [ "$OPTERR" == 1 ] && [ "${optspec:0:1}" != ":" ]; then
				    echo "Unknown option --${OPTARG}" >&2
				fi
				;;
			esac;;
		*)
			echo "Usage: $0 [-x|-m] [-G] [-w] [-k] [-j] [-v] [-r] [-e] [-l libs] [-f frontend] [-s script] [-p cmdstring] [-n iters] [-S seed] [-I incdir] [--xfirrtl FIRRTL test exclude file] [--firrtl2verilog command to generate verilog from firrtl] verilog-files\n" >&2
			exit 1
	esac
done

compile_and_run() {
	exe="$1"; output="$2"; shift 2
	if [ "${2##*.}" == "sv" ]; then
		language_gen="-g2012"
	else
		language_gen="-g2005"
	fi

	if $use_modelsim; then
		altver=$( ls -v /opt/altera/ | grep '^[0-9]' | tail -n1; )
		/opt/altera/$altver/modelsim_ase/bin/vlib work
		/opt/altera/$altver/modelsim_ase/bin/vlog $minclude_opts +define+outfile=\"$output\" "$@"
		/opt/altera/$altver/modelsim_ase/bin/vsim -c -do 'run -all; exit;' testbench
	elif $use_xsim; then
		xilver=$( ls -v /opt/Xilinx/Vivado/ | grep '^[0-9]' | tail -n1; )
		/opt/Xilinx/Vivado/$xilver/bin/xvlog $xinclude_opts -d outfile=\"$output\" "$@"
		/opt/Xilinx/Vivado/$xilver/bin/xelab -R work.testbench
	else
		iverilog $language_gen $include_opts -Doutfile=\"$output\" -s testbench -o "$exe" "$@"
		vvp -n "$exe"
	fi
}

shift $((OPTIND - 1))

for fn
do
	bn=${fn%.*}
	ext=${fn##*.}
	if [[ "$ext" != "v" ]] && [[ "$ext" != "sv" ]] && [[ "$ext" != "aag" ]] && [[ "$ext" != "aig" ]]; then
		echo "Invalid argument: $fn" >&2
		exit 1
	fi
	[[ "$bn" == *_tb ]] && continue

	if $makejmode; then
		status_prefix="Test: $bn "
	else
		status_prefix=""
		echo -n "Test: $bn "
	fi

	if [ "$ext" == sv ]; then
		frontend="$frontend -sv"
	fi

	rm -f ${bn}.{err,log,skip}
	mkdir -p ${bn}.out
	rm -rf ${bn}.out/*

	body() {
		cd ${bn}.out
		fn=$(basename $fn)
		bn=$(basename $bn)
		refext=v

		rm -f ${bn}_ref.fir
		if [[ "$ext" == "v" ]]; then
			egrep -v '^\s*`timescale' ../$fn > ${bn}_ref.${ext}
		elif [[ "$ext" == "aig" ]] || [[ "$ext" == "aag" ]]; then
			$abcprog -c "read_aiger ../${fn}; write ${bn}_ref.${refext}"
		else
			refext=$ext
			cp ../${fn} ${bn}_ref.${refext}
		fi

		if [ ! -f ../${bn}_tb.v ]; then
			"$toolsdir"/../../yosys -f "$frontend $include_opts -D_AUTOTB" -b "test_autotb $autotb_opts" -o ${bn}_tb.v ${bn}_ref.${refext}
		else
			cp ../${bn}_tb.v ${bn}_tb.v
		fi
		if $genvcd; then sed -i 's,// \$dump,$dump,g' ${bn}_tb.v; fi
		compile_and_run ${bn}_tb_ref ${bn}_out_ref ${bn}_tb.v ${bn}_ref.${refext} $libs \
					"$toolsdir"/../../techlibs/common/simlib.v \
					"$toolsdir"/../../techlibs/common/simcells.v
		if $genvcd; then mv testbench.vcd ${bn}_ref.vcd; fi

		test_count=0
		test_passes() {
			"$toolsdir"/../../yosys -b "verilog $backend_opts" -o ${bn}_syn${test_count}.v "$@"
			compile_and_run ${bn}_tb_syn${test_count} ${bn}_out_syn${test_count} \
					${bn}_tb.v ${bn}_syn${test_count}.v $libs \
					"$toolsdir"/../../techlibs/common/simlib.v \
					"$toolsdir"/../../techlibs/common/simcells.v
			if $genvcd; then mv testbench.vcd ${bn}_syn${test_count}.vcd; fi
			$toolsdir/cmp_tbdata ${bn}_out_ref ${bn}_out_syn${test_count}
			test_count=$(( test_count + 1 ))
		}

		if [ "$frontend" = "verific" -o "$frontend" = "verific_gates" ] && grep -q VERIFIC-SKIP ${bn}_ref.${refext}; then
			touch ../${bn}.skip
			return
		fi

		if [ -n "$scriptfiles" ]; then
			test_passes -f "$frontend $include_opts" ${bn}_ref.${refext} $scriptfiles
		elif [ -n "$scriptopt" ]; then
			test_passes -f "$frontend $include_opts" -p "$scriptopt" ${bn}_ref.${refext}
		elif [ "$frontend" = "verific" ]; then
			test_passes -p "verific -vlog2k ${bn}_ref.${refext}; verific -import -all; opt; memory;;"
		elif [ "$frontend" = "verific_gates" ]; then
			test_passes -p "verific -vlog2k ${bn}_ref.${refext}; verific -import -gates -all; opt; memory;;"
		else
			test_passes -f "$frontend $include_opts" -p "hierarchy; proc; opt; memory; opt; fsm; opt -full -fine" ${bn}_ref.${refext}
			test_passes -f "$frontend $include_opts" -p "hierarchy; synth -run coarse; techmap; opt; abc -dff" ${bn}_ref.${refext}
			if [ -n "$firrtl2verilog" ]; then
			    if test -z "$xfirrtl" || ! grep "$fn" "$xfirrtl" ; then
				"$toolsdir"/../../yosys -b "firrtl" -o ${bn}_ref.fir -f "$frontend $include_opts" -p "prep -nordff; proc; opt; memory; opt; fsm; opt -full -fine; pmuxtree" ${bn}_ref.${refext}
				$firrtl2verilog -i ${bn}_ref.fir -o ${bn}_ref.fir.v
				test_passes -f "$frontend $include_opts" -p "hierarchy; proc; opt; memory; opt; fsm; opt -full -fine" ${bn}_ref.fir.v
			    fi
			fi
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

	did_firrtl=""
	if [ -f ${bn}.out/${bn}_ref.fir ]; then
	    did_firrtl="+FIRRTL "
	fi
	if [ -f ${bn}.log ]; then
		mv ${bn}.err ${bn}.log
		echo "${status_prefix}${did_firrtl}-> ok"
	elif [ -f ${bn}.skip ]; then
		mv ${bn}.err ${bn}.skip
		echo "${status_prefix}-> skip"
	else
		echo "${status_prefix}${did_firrtl}-> ERROR!"
		if $warn_iverilog_git; then
			echo "Note: Make sure that 'iverilog' is an up-to-date git checkout of Icarus Verilog."
		fi
		$keeprunning || exit 1
	fi
done

exit 0
