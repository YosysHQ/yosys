`timescale 1ns/1ns 
module tb_dff();
	reg clk = 0;
	reg d = 0;
	wire q;

	dff uut(.clk(clk),.d(d),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_dff");
		$dumpvars(0,tb_dff);
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
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
