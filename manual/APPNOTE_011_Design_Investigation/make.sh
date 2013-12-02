#!/bin/bash
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
sed -i '/^label=/ d;' example_*.dot splice.dot cmos_*.dot sumprod_*.dot memdemo_*.dot submod_*.dot
dot -Tpdf -o example_00.pdf example_00.dot
dot -Tpdf -o example_01.pdf example_01.dot
dot -Tpdf -o example_02.pdf example_02.dot
dot -Tpdf -o example_03.pdf example_03.dot
dot -Tpdf -o splice.pdf splice.dot
dot -Tpdf -o cmos_00.pdf cmos_00.dot
dot -Tpdf -o cmos_01.pdf cmos_01.dot
dot -Tpdf -o sumprod_00.pdf sumprod_00.dot
dot -Tpdf -o sumprod_01.pdf sumprod_01.dot
dot -Tpdf -o sumprod_02.pdf sumprod_02.dot
dot -Tpdf -o sumprod_03.pdf sumprod_03.dot
dot -Tpdf -o sumprod_04.pdf sumprod_04.dot
dot -Tpdf -o sumprod_05.pdf sumprod_05.dot
dot -Tpdf -o memdemo_00.pdf memdemo_00.dot
dot -Tpdf -o memdemo_01.pdf memdemo_01.dot
dot -Tpdf -o submod_00.pdf submod_00.dot
dot -Tpdf -o submod_01.pdf submod_01.dot
dot -Tpdf -o submod_02.pdf submod_02.dot
dot -Tpdf -o submod_03.pdf submod_03.dot
