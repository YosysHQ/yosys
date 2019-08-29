set -e
if [ -f "../../techlibs/common/simcells.v" ]; then
	COMMON_PREFIX=../../techlibs/common
	TECHLIBS_PREFIX=../../techlibs
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
	echo "	@../../yosys -ql ${x%.ys}.log $x -w 'Yosys has only limited support for tri-state logic at the moment.'"

	if [ -f "${x%.ys}_tb.v" ]; then
		echo "	@echo 'Running ${x%.ys}_tb.v..'"
		echo "	@iverilog -o ${x%.ys}_testbench $t ${x%.ys}_synth.v common.v $TECHLIBS_PREFIX/ice40/cells_sim.v"
		echo "	@vvp -N ${x%.ys}_testbench"
	fi
done

#for s in *.sh; do
#	if [ "$s" != "run-test.sh" ]; then
#		echo "all:: run-$s"
#		echo "run-$s:"
#		echo "	@echo 'Running $s..'"
#		echo "	@bash $s"
#	fi
#done
} > run-test.mk
exec ${MAKE:-make} -f run-test.mk
