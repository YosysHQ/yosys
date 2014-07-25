module signed_test01(a, b, xu, xs, yu, ys, zu, zs);

input signed [1:0] a;
input signed [2:0] b;
output [3:0] xu, xs;
output [3:0] yu, ys;
output zu, zs;

assign xu = (a + b) + 3'd0;
assign xs = (a + b) + 3'sd0;

assign yu = {a + b} + 3'd0;
assign ys = {a + b} + 3'sd0;

assign zu = a + b != 3'd0;
assign zs = a + b != 3'sd0;

endmodule
