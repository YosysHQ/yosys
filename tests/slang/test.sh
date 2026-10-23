#!/usr/bin/env sh
set -eu

cd "$(dirname "$0")"

for dir in \
    asic/liberty \
    asic/abc_new \
    asic/abc_new/librelane \
    asic/abc_new/openroad \
    asic/techmap \
    basic \
    basic/opt \
    basic/peepopt \
    basic/proc \
    basic/svtypes \
    basic/various \
    basic/verific \
    basic/verilog \
    fpga/analogdevices \
    fpga/ecp5 \
    fpga/fabulous \
    fpga/gatemate \
    fpga/gowin \
    fpga/ice40 \
    fpga/machxo2 \
    fpga/quicklogic/qlf_k6n10f \
    fpga/xilinx
do
    (
        cd "$dir"
        python3 generate_mk.py
        make -j8
    )
done

sh formal/riscv-formal-dmem-check/rvf.sh
