
all: demo1 demo2

demo1: demo1.smt2
	yosys-smtbmc --dump-vcd demo1.vcd demo1.smt2
	yosys-smtbmc -i --dump-vcd demo1.vcd demo1.smt2

demo2: demo2.smt2
	yosys-smtbmc -g --dump-vcd demo2.vcd --dump-vlogtb demo2_tb.v --dump-constr demo2.smtc demo2.smt2
	iverilog -g2012 -o demo2_tb demo2_tb.v demo2.v
	vvp demo2_tb +vcd=demo2_tb.vcd

demo1.smt2: demo1.v
	yosys -p 'read_verilog -formal demo1.v; prep -top demo1 -nordff; write_smt2 -wires -mem -bv demo1.smt2'

demo2.smt2: demo2.v
	yosys -p 'read_verilog -formal demo2.v; prep -top demo2 -nordff; write_smt2 -wires -mem -bv demo2.smt2'

clean:
	rm -f demo1.smt2 demo1.vcd
	rm -f demo2.smt2 demo2.vcd demo2_tb.v demo2_tb demo2_tb.vcd

.PHONY: demo1 clean

