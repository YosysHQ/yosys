module test(a, b, c, d, y);
input [15:0] a, b;
input [31:0] c, d;
output [31:0] y;
assign y = a * b + c + d;
endmodule
