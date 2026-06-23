`timescale 1ns/1ns 
module tb_sdffce();
	reg clk = 0;
	reg rst = 0;
	reg d = 0;
	reg en = 0;
	wire q;

	sdffce uut(.clk(clk),.d(d),.rst(rst),.en(en),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_sdffce");
		$dumpvars(0,tb_sdffce);
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
