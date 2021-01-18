module Example(inp);
	input wire [3:0] inp;
	wire [3:0] fwd0 = inp;
	wire [4:1] fwd1 = inp;
	wire [5:2] fwd2 = inp;
	wire [6:3] fwd3 = inp;
	wire [0:3] rev0 = inp;
	wire [1:4] rev1 = inp;
	wire [2:5] rev2 = inp;
	wire [3:6] rev3 = inp;
endmodule

module gate(
	input wire [3:0] inp,
	output wire out0, out1, out2, out3, out4, out5, out6, out7
);
	Example m(inp);
	assign out0 = m.fwd0[3];
	assign out1 = m.fwd1[3];
	assign out2 = m.fwd2[3];
	assign out3 = m.fwd3[3];
	assign out4 = m.rev0[3];
	assign out5 = m.rev1[3];
	assign out6 = m.rev2[3];
	assign out7 = m.rev3[3];
endmodule

module gold(
	input wire [3:0] inp,
	output wire out0, out1, out2, out3, out4, out5, out6, out7
);
	assign out0 = inp[3];
	assign out1 = inp[2];
	assign out2 = inp[1];
	assign out3 = inp[0];
	assign out4 = inp[0];
	assign out5 = inp[1];
	assign out6 = inp[2];
	assign out7 = inp[3];
endmodule
