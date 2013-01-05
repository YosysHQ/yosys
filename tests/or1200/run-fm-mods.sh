#!/bin/bash
if [ -n "$REMOTE_YOSYS_ROOT" ]; then
	rsync --exclude=".svn" --exclude="*.log" -rv -e "${REMOTE_YOSYS_SSH:-ssh} -C" "$REMOTE_YOSYS_ROOT"/tests/or1200/. .
fi
for mod in $( grep '^module or1200_' synth.v | awk -F '[ (]' '{ print $2; }'; )
do
	{
		grep '^set ' run-fm.do
		grep '^read_verilog -container r ' run-fm.do
		echo "set_top r:/WORK/$mod"
		grep '^read_verilog -container i ' run-fm.do
		echo "set_top i:/WORK/$mod"
		echo "verify"
		echo "exit"
	} > run-fm-${mod}.do
	fm_shell -64 -file run-fm-${mod}.do 2>&1 | tee run-fm-${mod}.log
	rsync -v -e "${REMOTE_YOSYS_SSH:-ssh}" run-fm-${mod}.log "$REMOTE_YOSYS_ROOT"/tests/or1200/
done

echo; echo
for x in run-fm-*.log; do
	echo -e "${x%/*}\\t$( egrep '^Verification (SUCCEEDED|FAILED)' $x; )"
done | expand -t20
echo; echo
