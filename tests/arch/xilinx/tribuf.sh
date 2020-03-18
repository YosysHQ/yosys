! ../../../yosys -qp "synth_xilinx" ../common/tribuf.v
../../../yosys -qp "synth_xilinx -iopad; \
select -assert-count 2 t:IBUF; \
select -assert-count 1 t:INV; \
select -assert-count 1 t:OBUFT" ../common/tribuf.v
