module abc9_test001(input a, output o);
assign o = a;
endmodule

module abc9_test002(input [1:0] a, output o);
assign o = a[1];
endmodule

module abc9_test003(input [1:0] a, output [1:0] o);
assign o = a;
endmodule

module abc9_test004(input [1:0] a, output o);
assign o = ^a;
endmodule

module abc9_test005(input [1:0] a, output o, output p);
assign o = ^a;
assign p = ~o;
endmodule

module abc9_test006(input [1:0] a, output [2:0] o);
assign o[0] = ^a;
assign o[1] = ~o[0];
assign o[2] = o[1];
endmodule

module abc9_test007(input a, output o);
wire b, c;
assign c = ~a;
assign b = c;
abc9_test007_sub s(b, o);
endmodule

module abc9_test007_sub(input a, output b);
assign b = a;
endmodule

module abc9_test008(input a, output o);
wire b, c;
assign b = ~a;
assign c = b;
abc9_test008_sub s(b, o);
endmodule

module abc9_test008_sub(input a, output b);
assign b = ~a;
endmodule
