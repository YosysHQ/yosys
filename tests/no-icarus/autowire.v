
module test01(a, b, y);

input [3:0] a, b;
output [3:0] y;

assign temp1 = a + b;
assign temp2 = ~temp1;
assign y = temp2;

endmodule

// ------------------------------

module test02(a, b, y);

input [3:0] a, b;
output [3:0] y;

test01 test01_cell(A, B, Y);

assign A = a, B = b, y = Y;

endmodule

