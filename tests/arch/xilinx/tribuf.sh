! ../../../yosys ../common/tribuf.v -qp "synth_xilinx"
../../../yosys ../common/tribuf.v -qp "synth_xilinx -iopad; \
select -assert-count 2 t:IBUF; \
select -assert-count 1 t:INV; \
select -assert-count 1 t:OBUFT"
