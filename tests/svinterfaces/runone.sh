#!/bin/bash


TESTNAME=$1

STDOUTFILE=${TESTNAME}.log_stdout
STDERRFILE=${TESTNAME}.log_stderr

echo "" > $STDOUTFILE
echo "" > $STDERRFILE

echo -n "Test: ${TESTNAME} -> "

set -e

$PWD/../../yosys -p "read_verilog -sv ${TESTNAME}.sv ; hierarchy -check -top TopModule ; synth ; write_verilog ${TESTNAME}_syn.v" >> $STDOUTFILE 2>> $STDERRFILE
$PWD/../../yosys -p "read_verilog -sv ${TESTNAME}_ref.v ; hierarchy -check -top TopModule ; synth ; write_verilog ${TESTNAME}_ref_syn.v" >> $STDOUTFILE 2>> $STDERRFILE

rm -f a.out reference_result.txt dut_result.txt

iverilog -g2012 ${TESTNAME}_syn.v
iverilog -g2012 ${TESTNAME}_ref_syn.v

set +e
iverilog -g2012 ${TESTNAME}_tb.v ${TESTNAME}_ref_syn.v
./a.out
mv output.txt reference_result.txt
if [ -f ${TESTNAME}_wrapper.v ] ; then
    iverilog -g2012 ${TESTNAME}_tb_wrapper.v ${TESTNAME}_syn.v
else
    iverilog -g2012 ${TESTNAME}_tb.v ${TESTNAME}_syn.v
fi
./a.out
mv output.txt dut_result.txt

diff reference_result.txt dut_result.txt > ${TESTNAME}.diff
RET=$?
if [ "$RET" != "0" ] ; then
    echo "ERROR!"
    exit -1
fi

echo "ok"
exit 0
