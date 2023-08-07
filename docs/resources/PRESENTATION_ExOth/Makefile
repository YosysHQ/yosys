YOSYS = ../../../yosys

all: scrambler_p01.pdf scrambler_p02.pdf equiv.log axis_test.log

scrambler_p01.pdf: scrambler.ys scrambler.v
	$(YOSYS) scrambler.ys

scrambler_p02.pdf: scrambler_p01.pdf

equiv.log: equiv.ys
	$(YOSYS) -l equiv.log_new equiv.ys
	mv equiv.log_new equiv.log

axis_test.log: axis_test.ys axis_master.v axis_test.v
	$(YOSYS) -l axis_test.log_new axis_test.ys
	mv axis_test.log_new axis_test.log

