#!/bin/bash
set -ex
if false; then
	rm -f *.dot
	../../yosys example.ys
	../../yosys -p 'proc; opt; show -format dot -prefix splice' splice.v
	../../yosys -p 'techmap; abc -liberty ../../techlibs/cmos/cmos_cells.lib;; show -format dot -prefix cmos_00' cmos.v
	../../yosys -p 'techmap; splitnets -ports; abc -liberty ../../techlibs/cmos/cmos_cells.lib;; show -lib ../../techlibs/cmos/cmos_cells.v -format dot -prefix cmos_01' cmos.v
	../../yosys -p 'opt; cd sumprod; select a:sumstuff; show -format dot -prefix sumprod_00' sumprod.v
	../../yosys -p 'opt; cd sumprod; select a:sumstuff %x; show -format dot -prefix sumprod_01' sumprod.v
	../../yosys -p 'opt; cd sumprod; select prod; show -format dot -prefix sumprod_02' sumprod.v
	../../yosys -p 'opt; cd sumprod; select prod %ci; show -format dot -prefix sumprod_03' sumprod.v
	../../yosys -p 'opt; cd sumprod; select prod %ci2; show -format dot -prefix sumprod_04' sumprod.v
	../../yosys -p 'opt; cd sumprod; select prod %ci3; show -format dot -prefix sumprod_05' sumprod.v
	../../yosys -p 'proc; opt; memory; opt; cd memdemo; show -format dot -prefix memdemo_00' memdemo.v
	../../yosys -p 'proc; opt; memory; opt; cd memdemo; show -format dot -prefix memdemo_01 y %ci2:+$dff[Q,D] %ci*:-$mux[S]:-$dff' memdemo.v
	../../yosys submod.ys
	sed -i '/^label=/ d;' *.dot
fi
for dot_file in *.dot; do
	pdf_file=${dot_file%.dot}.pdf
	dot -Tpdf -o $pdf_file $dot_file
done
