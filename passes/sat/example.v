
module example(a, y);

input [15:0] a;
output y;

wire gt = a > 12345;
wire lt = a < 12345;
assign y = !gt && !lt;

endmodule

