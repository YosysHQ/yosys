module pass_through #(
	parameter WIDTH = 1
) (
	input logic [WIDTH-1:0] inp,
	output logic [WIDTH-1:0] out
);
	assign out = inp;
endmodule

module gate (
	input logic inp,
	output logic [63:0]
		out1, out2, out3, out4
);
	pass_through #(40) pt1('1, out1);
	pass_through #(40) pt2(inp ? '1 : '0, out2);
	pass_through #(40) pt3(inp ? '1 : 2'b10, out3);
	pass_through #(40) pt4(inp ? '1 : inp, out4);
endmodule

module gold (
	input logic inp,
	output logic [63:0]
		out1, out2, out3, out4
);
	localparam ONES = 40'hFF_FFFF_FFFF;
	pass_through #(40) pt1(ONES, out1);
	pass_through #(40) pt2(inp ? ONES : 0, out2);
	pass_through #(40) pt3(inp ? ONES : 2'sb10, out3);
	pass_through #(40) pt4(inp ? ONES : inp, out4);
endmodule
