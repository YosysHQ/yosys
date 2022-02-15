`timescale 1ns/1ns 
module tb_dffsr();
	reg clk = 0;
	reg d = 0;
	reg set = 0;
	reg clr = 0;
	wire q;

	dffsr uut(.d(d),.clk(clk),.set(set),.clr(clr),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_dffsr");
		$dumpvars(0,tb_dffsr);
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		clr = 1;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		clr = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		set = 1;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		set = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		$finish;
	end
endmodule
