module test(out, i0, i1, i2, i3, s1, s0);
output out;
input i0, i1, i2, i3;
input s1, s0;

assign out = (~s1 & s0 & i0) |
			 (~s1 & s0 & i1) |
			 (s1 & ~s0 & i2) |
			 (s1 & s0 & i3);

endmodule

module ternaryop(out, i0, i1, i2, i3, s1, s0);
output out;
input i0, i1, i2, i3;
input s1, s0;

assign out = s1 ? (s0 ? i3 : i2) : (s0 ? i1 : i0);

endmodule

module fulladd4(sum, c_out, a, b, c_in);
output [3:0] sum;
output c_out;
input [3:0] a, b;
input c_in;

assign {c_out, sum} = a + b + c_in;
endmodule
