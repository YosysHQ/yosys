module Example(inp);
	input wire [3:0] inp;
	wire signed [3:0] sgn = inp;
	wire [3:0] uns = inp;
endmodule

module gate(inp, out1, out2);
	input wire [3:0] inp;
	output wire [7:0] out1, out2;

	Example m(inp);
	assign out1 = m.sgn;
	assign out2 = m.uns;
endmodule

module gold(inp, out1, out2);
	input wire [3:0] inp;
	output wire [7:0] out1, out2;

	assign out1 = $signed(inp);
	assign out2 = $unsigned(inp);
endmodule
