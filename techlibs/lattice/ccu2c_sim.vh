// ---------------------------------------
(* abc9_box, lib_whitebox *)
module CCU2C(
	(* abc9_carry *)
	input  CIN,
	input  A0, B0, C0, D0, A1, B1, C1, D1,
	output S0, S1,
	(* abc9_carry *)
	output COUT
);
	parameter [15:0] INIT0 = 16'h0000;
	parameter [15:0] INIT1 = 16'h0000;
	parameter INJECT1_0 = "YES";
	parameter INJECT1_1 = "YES";

	// First half
	wire LUT4_0, LUT2_0;
	LUT4 #(.INIT(INIT0)) lut4_0(.A(A0), .B(B0), .C(C0), .D(D0), .Z(LUT4_0));
	LUT2 #(.INIT(INIT0[3:0])) lut2_0(.A(A0), .B(B0), .Z(LUT2_0));
	wire gated_cin_0 = (INJECT1_0 == "YES") ? 1'b0 : CIN;
	assign S0 = LUT4_0 ^ gated_cin_0;

	wire gated_lut2_0 = (INJECT1_0 == "YES") ? 1'b0 : LUT2_0;
	wire cout_0 = (~LUT4_0 & gated_lut2_0) | (LUT4_0 & CIN);

	// Second half
	wire LUT4_1, LUT2_1;
	LUT4 #(.INIT(INIT1)) lut4_1(.A(A1), .B(B1), .C(C1), .D(D1), .Z(LUT4_1));
	LUT2 #(.INIT(INIT1[3:0])) lut2_1(.A(A1), .B(B1), .Z(LUT2_1));
	wire gated_cin_1 = (INJECT1_1 == "YES") ? 1'b0 : cout_0;
	assign S1 = LUT4_1 ^ gated_cin_1;

	wire gated_lut2_1 = (INJECT1_1 == "YES") ? 1'b0 : LUT2_1;
	assign COUT = (~LUT4_1 & gated_lut2_1) | (LUT4_1 & cout_0);

	specify
		(A0 => S0) = 379;
		(B0 => S0) = 379;
		(C0 => S0) = 275;
		(D0 => S0) = 141;
		(CIN => S0) = 257;
		(A0 => S1) = 630;
		(B0 => S1) = 630;
		(C0 => S1) = 526;
		(D0 => S1) = 392;
		(A1 => S1) = 379;
		(B1 => S1) = 379;
		(C1 => S1) = 275;
		(D1 => S1) = 141;
		(CIN => S1) = 273;
		(A0 => COUT) = 516;
		(B0 => COUT) = 516;
		(C0 => COUT) = 412;
		(D0 => COUT) = 278;
		(A1 => COUT) = 516;
		(B1 => COUT) = 516;
		(C1 => COUT) = 412;
		(D1 => COUT) = 278;
		(CIN => COUT) = 43;
	endspecify
endmodule
