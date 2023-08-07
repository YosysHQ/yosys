module DSP48_MACC (a, b, c, y);

input [17:0] a;
input [24:0] b;
input [47:0] c;
output [47:0] y;

assign y = a*b + c;

endmodule
