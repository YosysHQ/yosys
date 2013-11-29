#!/bin/bash
../../yosys example.ys
../../yosys -p 'proc; opt; show -format dot -prefix splice' splice.v
../../yosys -p 'techmap; abc -liberty ../../techlibs/cmos/cmos_cells.lib;; show -format dot -prefix cmos_00' cmos.v
../../yosys -p 'techmap; splitnets -ports; abc -liberty ../../techlibs/cmos/cmos_cells.lib;; show -lib ../../techlibs/cmos/cmos_cells.v -format dot -prefix cmos_01' cmos.v
../../yosys -p 'opt; cd sumprod; select a:sumstuff; show -format dot -prefix sumprod_00' sumprod.v
../../yosys -p 'opt; cd sumprod; select a:sumstuff %x; show -format dot -prefix sumprod_01' sumprod.v
sed -i '/^label=/ d;' example_*.dot splice.dot cmos_*.dot sumprod_*.dot
dot -Tpdf -o example_00.pdf example_00.dot
dot -Tpdf -o example_01.pdf example_01.dot
dot -Tpdf -o example_02.pdf example_02.dot
dot -Tpdf -o example_03.pdf example_03.dot
dot -Tpdf -o splice.pdf splice.dot
dot -Tpdf -o cmos_00.pdf cmos_00.dot
dot -Tpdf -o cmos_01.pdf cmos_01.dot
dot -Tpdf -o sumprod_00.pdf sumprod_00.dot
dot -Tpdf -o sumprod_01.pdf sumprod_01.dot
