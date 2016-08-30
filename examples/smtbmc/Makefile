
all: demo1 demo2 demo3 demo4

demo1: demo1.smt2
	yosys-smtbmc --dump-vcd demo1.vcd demo1.smt2
	yosys-smtbmc -i --dump-vcd demo1.vcd demo1.smt2

demo2: demo2.smt2
	yosys-smtbmc -g --dump-vcd demo2.vcd --dump-smtc demo2.smtc --dump-vlogtb demo2_tb.v demo2.smt2
	iverilog -g2012 -o demo2_tb demo2_tb.v demo2.v
	vvp demo2_tb +vcd=demo2_tb.vcd

demo3: demo3.smt2
	yosys-smtbmc --dump-vcd demo3.vcd --smtc demo3.smtc demo3.smt2

demo4: demo4.smt2
	yosys-smtbmc -s yices --dump-vcd demo4.vcd --smtc demo4.smtc demo4.smt2

demo1.smt2: demo1.v
	yosys -ql demo1.yslog -p 'read_verilog -formal demo1.v; prep -top demo1 -nordff; write_smt2 -wires demo1.smt2'

demo2.smt2: demo2.v
	yosys -ql demo2.yslog -p 'read_verilog -formal demo2.v; prep -top demo2 -nordff; write_smt2 -wires demo2.smt2'

demo3.smt2: demo3.v
	yosys -ql demo3.yslog -p 'read_verilog -formal demo3.v; prep -top demo3 -nordff; write_smt2 -wires demo3.smt2'

demo4.smt2: demo4.v
	yosys -ql demo4.yslog -p 'read_verilog -formal demo4.v; prep -top demo4 -nordff; write_smt2 -wires demo4.smt2'

clean:
	rm -f demo1.yslog demo1.smt2 demo1.vcd
	rm -f demo2.yslog demo2.smt2 demo2.vcd demo2.smtc demo2_tb.v demo2_tb demo2_tb.vcd
	rm -f demo3.yslog demo3.smt2 demo3.vcd
	rm -f demo4.yslog demo4.smt2 demo4.vcd

.PHONY: demo1 demo2 demo3 demo4 clean

