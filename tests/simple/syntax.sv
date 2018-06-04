// Implied name ports
module alu (
	// from SV2012 spec
	output reg [7:0] alu_out,
	output reg zero,
	input [7:0] ain, bin,
	input [2:0] opcode
	);
endmodule

module named_port;
	wire [7:0] alu_out;
	wire [7:0] ain, bin;
	wire [2:0] opcode;

	alu alu (
		.alu_out(alu_out),
		.zero(),	// zero output is unconnected
		.ain,		// implicit named port connected to alu.ain
		.bin(bin),
		.opcode
	);
endmodule

module array_sizes;
	reg [31:0] old_way[0:15];
	reg [31:0] new_way[16];
endmodule
