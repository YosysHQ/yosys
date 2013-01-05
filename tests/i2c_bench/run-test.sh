#!/bin/bash

set -e
make -C ../..
../../yosys -l i2c_master_syn.log -o i2c_master_syn.v \
		-p hierarchy -p proc -p memory -p techmap -p opt -p abc -p opt \
		i2c_master_top.v i2c_master_bit_ctrl.v i2c_master_byte_ctrl.v
. /opt/Xilinx/13.4/ISE_DS/settings64.sh

vlogcomp --work ref i2c_master_bit_ctrl.v
vlogcomp --work ref i2c_master_byte_ctrl.v
vlogcomp --work ref i2c_master_top.v
vlogcomp --work ref i2c_slave_model.v
vlogcomp --work ref spi_slave_model.v
vlogcomp --work ref tst_bench_top.v
vlogcomp --work ref wb_master_model.v
fuse --work ref -o testbench_ref --top tst_bench_top

cat > testbench_ref.tcl << EOT
vcd dumpfile testbench_ref.vcd
vcd dumpvars -m tst_bench_top -l 0
vcd dumpon
run 2 ms
exit
EOT

./testbench_ref -tclbatch testbench_ref.tcl

vlogcomp --work syn i2c_master_syn.v
vlogcomp --work syn ../../techlibs/simlib.v
vlogcomp --work syn ../../techlibs/stdcells_sim.v
vlogcomp --work syn i2c_slave_model.v
vlogcomp --work syn spi_slave_model.v
vlogcomp --work syn tst_bench_top.v
vlogcomp --work syn wb_master_model.v
fuse --work syn -o testbench_syn --top tst_bench_top

cat > testbench_syn.tcl << EOT
vcd dumpfile testbench_syn.vcd
vcd dumpvars -m tst_bench_top -l 0
vcd dumpon
run 2 ms
exit
EOT

./testbench_syn -tclbatch testbench_syn.tcl

perl ../tools/vcdcd.pl testbench_ref.vcd testbench_syn.vcd | tee testbench_diff.txt
echo READY.

