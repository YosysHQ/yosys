
module test1(input clk, input [3:0] a, output reg [3:0] y);
always @(posedge clk)
	y <= a;
endmodule

module test2(input clk, input [3:0] a, output reg [3:0] y);
wire clk_n = !clk;
always @(negedge clk_n)
	y[1:0] <= a[1:0];
always @(negedge clk_n)
	y[3:2] <= a[3:2];
endmodule

// -----------------------------------------------------------

module test3(input clk, rst, input [3:0] a, output reg [3:0] y);
always @(posedge clk, posedge rst)
	if (rst)
		y <= 12;
	else
		y <= |a;
endmodule

module test4(input clk, rst, input [3:0] a, output reg [3:0] y);
wire rst_n = !rst;
always @(posedge clk, negedge rst_n)
	if (!rst_n)
		y <= 12;
	else
		y <= a != 0;
endmodule

