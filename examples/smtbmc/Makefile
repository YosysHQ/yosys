
demo1: demo1.smt2
	yosys-smtbmc -c demo1.vcd demo1.smt2
	yosys-smtbmc -i -c demo1.vcd demo1.smt2

demo1.smt2: demo1.v
	yosys -p 'read_verilog -formal demo1.v; prep -top demo1; write_smt2 -wires -mem -bv demo1.smt2'

clean:
	rm -f demo1.smt2

.PHONY: demo1 clean

