set -e
if [ -f "../../../../../techlibs/common/simcells.v" ]; then
	COMMON_PREFIX=../../../../../techlibs/common
	TECHLIBS_PREFIX=../../../../../techlibs
else
	COMMON_PREFIX=/usr/local/share/yosys
	TECHLIBS_PREFIX=/usr/local/share/yosys
fi
{
echo "all::"
for x in *.ys; do
	echo "all:: run-$x"
	echo "run-$x:"
	echo "	@echo 'Running $x..'"
	echo "	@../../yosys -ql ${x%.ys}.log $x"
done
for t in *_tb.v; do
	echo "all:: run-$t"
	echo "run-$t:"
	echo "	@echo 'Running $t..'"
	echo "	@iverilog -o ${t%_tb.v}_testbench  $t ${t%_tb.v}_synth.v common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v"
	echo "	@if ! vvp -N ${t%_tb.v}_testbench > ${t%_tb.v}_testbench.log 2>&1; then grep 'ERROR' ${t%_tb.v}_testbench.log; exit 0; elif grep 'ERROR' ${t%_tb.v}_testbench.log || ! grep 'OKAY' ${t%_tb.v}_testbench.log; then echo "FAIL"; exit 0; fi"
done
for s in *.sh; do
	if [ "$s" != "run-test.sh" ]; then
		echo "all:: run-$s"
		echo "run-$s:"
		echo "	@echo 'Running $s..'"
		echo "	@bash $s"
	fi
done
} > run-test.mk
exec ${MAKE:-make} -f run-test.mk
