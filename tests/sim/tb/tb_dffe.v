`timescale 1ns/1ns 
module tb_dffe();
	reg clk = 0;
	reg en = 0;
	reg d = 0;
	wire q;

	dffe uut(.clk(clk),.d(d),.en(en),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_dffe");
		$dumpvars(0,tb_dffe);
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		en = 1;
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
