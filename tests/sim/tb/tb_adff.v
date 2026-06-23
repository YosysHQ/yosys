`timescale 1ns/1ns 
module tb_adff();
	reg clk = 0;
	reg rst = 0;
	reg d = 0;
	wire q;

	adff uut(.clk(clk),.d(d),.rst(rst),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_adff");
		$dumpvars(0,tb_adff);
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
