`default_nettype none

module \$reduce_and (A, Y);
	parameter A_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter Y_WIDTH = 0;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	// Since routing the carry in and out requires 2 CCU2Cs, and a LUT6 is only
	// four LUT4s, this is only worth it at 7 inputs and beyond.
	wire _TECHMAP_FAIL_ = A_WIDTH <= 6;

	localparam WIDTH8 = ((A_WIDTH + 7) / 8);

	(* force_downto *)
	wire [8*WIDTH8-1:0] AA = {7'b1111111, A};
	(* force_downto *)
	wire [WIDTH8:0] CARRY;
	assign CARRY[0] = 1'b1;

	genvar i;
	generate for (i = 0; i < WIDTH8; i = i + 1) begin:slice
		CCU2C #(
			.INIT0(16'h8000),
			.INIT1(16'h8000),
			.INJECT1_0("NO"),
			.INJECT1_1("NO")
		) ccu2_i (
			.CIN(CARRY[i]),
			.A0(AA[8*i]), .B0(AA[8*i+1]), .C0(AA[8*i+2]), .D0(AA[8*i+3]),
			.A1(AA[8*i+4]), .B1(AA[8*i+5]), .C1(AA[8*i+6]), .D1(AA[8*i+7]),
			.S0(), .S1(),
			.COUT(CARRY[i+1])
		);
	end endgenerate

	assign Y = CARRY[WIDTH8];
endmodule

// Reduce-OR is implemented through De Morgan's laws as a Reduce-AND.

module \$reduce_or (A, Y);
	parameter A_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter Y_WIDTH = 0;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	// Since routing the carry in and out requires 2 CCU2Cs, and a LUT6 is only
	// four LUT4s, this is only worth it at 7 inputs and beyond.
	wire _TECHMAP_FAIL_ = A_WIDTH <= 6;

	localparam WIDTH8 = ((A_WIDTH + 7) / 8);

	(* force_downto *)
	wire [8*WIDTH8-1:0] AA = {7'b0000000, A};
	(* force_downto *)
	wire [WIDTH8:0] CARRY;
	assign CARRY[0] = 1'b1;

	genvar i;
	generate for (i = 0; i < WIDTH8; i = i + 1) begin:slice
		CCU2C #(
			.INIT0(16'h0001),
			.INIT1(16'h0001),
			.INJECT1_0("YES"),
			.INJECT1_1("YES")
		) ccu2_i (
			.CIN(CARRY[i]),
			.A0(AA[8*i]), .B0(AA[8*i+1]), .C0(AA[8*i+2]), .D0(AA[8*i+3]),
			.A1(AA[8*i+4]), .B1(AA[8*i+5]), .C1(AA[8*i+6]), .D1(AA[8*i+7]),
			.S0(), .S1(),
			.COUT(CARRY[i+1])
		);
	end endgenerate

	// nextpnr would produce a CCU2C to output the carry anyway, so fold the
	// output inverter into it.
	CCU2C #(
		.INIT0(16'hffff),
		.INIT1(16'h0000),
		.INJECT1_0("NO"),
		.INJECT1_1("NO"),
	) inverter (
		.CIN(CARRY[WIDTH8]),
		.A0(1'b1), .B0(1'b1), .C0(1'b1), .D0(1'b1),
		.A1(1'b1), .B1(1'b1), .C1(1'b1), .D1(1'b1),
		.S0(Y), .S1(),
		.COUT()
	);
endmodule
