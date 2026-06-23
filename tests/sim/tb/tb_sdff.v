`timescale 1ns/1ns 
module tb_sdff();
	reg clk = 0;
	reg rst = 0;
	reg d = 0;
	wire q;

	sdff uut(.clk(clk),.d(d),.rst(rst),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_sdff");
		$dumpvars(0,tb_sdff);
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		rst = 1;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		rst = 0;
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
