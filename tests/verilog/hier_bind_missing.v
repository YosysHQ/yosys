module Example(inp);
	input wire [3:0] inp;
	wire [3:0] exists = inp;
endmodule

module top(
	input wire [3:0] inp,
	output wire [3:0] out
);
	Example m(inp);
	assign out = m.does_not_exist & m.exists;
endmodule
