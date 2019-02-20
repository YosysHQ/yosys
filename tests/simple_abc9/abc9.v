module top(input [1:0] a, output [1:0] b, output c, output d, output e);
assign b = a;
assign c = ^a;
assign d = ~c;
assign e = d;
endmodule
