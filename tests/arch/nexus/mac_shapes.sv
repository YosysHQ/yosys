// https://github.com/YosysHQ/yosys/issues/6233

module mac36_add (input [23:0] a, b, input [40:0] c, output [47:0] y);
	assign y = a * b + c;
endmodule

module mac36_sub (input [23:0] a, b, input [70:0] c, output [70:0] y);
	assign y = c - a * b;
endmodule

// Product is the minuend. The DSP can only do C +/- A*B.
module mac36_subrev (input [23:0] a, b, input [40:0] c, output [47:0] y);
	assign y = a * b - c;
endmodule

// Narrower than 36 bits: the 18-bit MAC must still win.
module mac18_still (input [15:0] a, b, input [20:0] c, output [31:0] y);
	assign y = a * b + c;
endmodule

// Signed product, zero-extended unsigned offset.
module mac36_mix (input signed [19:0] a, b, input [31:0] c, output signed [51:0] y);
	assign y = a * b + $signed({1'b0, c});
endmodule

module dot4_acc (
	input [7:0] a0, b0, a1, b1, a2, b2, a3, b3,
	input [31:0] c,
	output [47:0] y
);
	assign y = a0*b0 + a1*b1 + a2*b2 + a3*b3 + c;
endmodule
