// ---------------------------------------
(* lib_whitebox *)
module CCU2D (
	input  CIN,
	input  A0, B0, C0, D0, A1, B1, C1, D1,
	output S0, S1,
	output COUT
);
	parameter [15:0] INIT0 = 16'h0000;
	parameter [15:0] INIT1 = 16'h0000;
	parameter INJECT1_0 = "YES";
	parameter INJECT1_1 = "YES";

	// First half
	wire LUT4_0, LUT2_0;
	LUT4 #(.INIT(INIT0)) lut4_0(.A(A0), .B(B0), .C(C0), .D(D0), .Z(LUT4_0));
	LUT2 #(.INIT(~INIT0[15:12])) lut2_0(.A(A0), .B(B0), .Z(LUT2_0));
	wire gated_cin_0 = (INJECT1_0 == "YES") ? 1'b0 : CIN;
	assign S0 = LUT4_0 ^ gated_cin_0;

	wire gated_lut2_0 = (INJECT1_0 == "YES") ? 1'b0 : LUT2_0;
	wire cout_0 = (~LUT4_0 & gated_lut2_0) | (LUT4_0 & CIN);

	// Second half
	wire LUT4_1, LUT2_1;
	LUT4 #(.INIT(INIT1)) lut4_1(.A(A1), .B(B1), .C(C1), .D(D1), .Z(LUT4_1));
	LUT2 #(.INIT(~INIT1[15:12])) lut2_1(.A(A1), .B(B1), .Z(LUT2_1));
	wire gated_cin_1 = (INJECT1_1 == "YES") ? 1'b0 : cout_0;
	assign S1 = LUT4_1 ^ gated_cin_1;

	wire gated_lut2_1 = (INJECT1_1 == "YES") ? 1'b0 : LUT2_1;
	assign COUT = (~LUT4_1 & gated_lut2_1) | (LUT4_1 & cout_0);
endmodule
