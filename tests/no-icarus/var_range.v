
module test01(a, b, x, y, z);

input [7:0] a;
input [2:0] b;
output [7:0] x, y;
output z;

assign x = a >> b;
assign y = a[b+7:b];
assign z = a[b];

endmodule

module test02(clk, a, b, x, y, z);

input clk;
input [7:0] a;
input [2:0] b;
output reg [7:0] x, y;
output reg z;

always @(posedge clk) begin
	x <= a >> b;
	y <= a[b+7:b];
	z <= a[b];
end

endmodule

module test03(clk, a, b, x, y);

input clk;
input [2:0] a, b;
output reg [7:0] x;
output reg [9:0] y;

always @(posedge clk)
	y[b] <= a;

always @(posedge clk)
	y[b+2:b] <= a;

endmodule

