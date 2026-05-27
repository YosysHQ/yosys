module mixed_vector_decode(
	input  [2:0] sel0,
	input  [2:0] sel1,
	input  [3:0] a0,
	input  [3:0] b0,
	input  [3:0] c0,
	input  [3:0] a1,
	input  [3:0] b1,
	input  [3:0] c1,
	output [3:0] y0,
	output [3:0] y1
);
	assign {y1, y0} =
		({ {4{sel1 == 3'd1}}, {4{sel0 == 3'd1}} } & {a1, a0}) |
		({ {4{sel1 == 3'd2}}, {4{sel0 == 3'd2}} } & {b1, b0}) |
		({ {4{sel1 == 3'd3}}, {4{sel0 == 3'd3}} } & {c1, c0});
endmodule

module partial_vector_decode(
	input  [2:0] sel0,
	input  [2:0] sel1,
	input  [3:0] a0,
	input  [3:0] b0,
	input  [3:0] c0,
	input  [3:0] a1,
	input  [3:0] b1,
	input  [3:0] c1,
	input  [3:0] passthru,
	output [3:0] y0,
	output [3:0] y1
);
	wire [7:0] stage =
		({ {4{sel1 == 3'd1}}, {4{sel0 == 3'd1}} } & {a1, a0}) |
		({ {4{sel1 == 3'd2}}, {4{sel0 == 3'd2}} } & {b1, b0}) |
		({ {4{sel1 == 3'd3}}, {4{sel0 == 3'd3}} } & {c1, c0});

	assign y1 = stage[7:4];
	assign y0 = stage[3:0] | passthru;
endmodule

module tiny_decode(
	input  [1:0] sel,
	input        a,
	input        b,
	output       y
);
	assign y = ((sel == 2'd1) & a) | ((sel == 2'd2) & b);
endmodule
