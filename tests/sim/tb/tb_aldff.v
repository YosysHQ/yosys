`timescale 1ns/1ns 
module tb_aldff();
	reg clk = 0;
	reg aload = 0;
	reg [0:3] d  = 4'b0000;
	reg [0:3] ad = 4'b1010;
	wire [0:3] q;

	aldff uut(.clk(clk),.d(d),.ad(ad),.aload(aload),.q(q));

	always
		#(5) clk <= !clk;

	initial
	begin
		$dumpfile("tb_aldff");
		$dumpvars(0,tb_aldff);
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		aload = 1;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		aload = 0;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		aload = 1;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		aload = 0;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		d = 4'b1100;
		#10
		d = 4'b0011;
		#10
		$finish;
	end
endmodule
