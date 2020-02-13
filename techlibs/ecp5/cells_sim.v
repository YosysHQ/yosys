// ---------------------------------------

(* abc9_lut=1, lib_whitebox *)
module LUT4(input A, B, C, D, output Z);
    parameter [15:0] INIT = 16'h0000;
    wire [7:0] s3 = D ?     INIT[15:8] :     INIT[7:0];
    wire [3:0] s2 = C ?       s3[ 7:4] :       s3[3:0];
    wire [1:0] s1 = B ?       s2[ 3:2] :       s2[1:0];
    assign Z =      A ?          s1[1] :         s1[0];
    specify
        (A => Z) = 141;
        (B => Z) = 275;
        (C => Z) = 379;
        (D => Z) = 379;
    endspecify
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 5-input LUTs and is not intended to be instantiated
// LUT5 = 2x LUT4 + PFUMX
(* abc9_lut=2 *)
module \$__ABC9_LUT5 (input M0, D, C, B, A, output Z);
    specify
        (M0 => Z) = 151;
        (D => Z) = 239;
        (C => Z) = 373;
        (B => Z) = 477;
        (A => Z) = 477;
    endspecify
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   of 6-input LUTs and is not intended to be instantiated
// LUT6 = 2x LUT5 + MUX2
(* abc9_lut=4 *)
module \$__ABC9_LUT6 (input M1, M0, D, C, B, A, output Z);
    specify
        (M1 => Z) = 148;
        (M0 => Z) = 292;
        (D => Z) = 380;
        (C => Z) = 514;
        (B => Z) = 618;
        (A => Z) = 618;
    endspecify
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   of 7-input LUTs and is not intended to be instantiated
// LUT7 = 2x LUT6 + MUX2
(* abc9_lut=8 *)
module \$__ABC9_LUT7 (input M2, M1, M0, D, C, B, A, output Z);
    specify
        (M2 => Z) = 148;
        (M1 => Z) = 289;
        (M0 => Z) = 433;
        (D => Z) = 521;
        (C => Z) = 655;
        (B => Z) = 759;
        (A => Z) = 759;
    endspecify
endmodule

// ---------------------------------------
(* abc9_box, lib_whitebox *)
module L6MUX21 (input D0, D1, SD, output Z);
	assign Z = SD ? D1 : D0;
	specify
		(D0 => Z) = 140;
		(D1 => Z) = 141;
		(SD => Z) = 148;
	endspecify
endmodule

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

// ---------------------------------------

module TRELLIS_RAM16X2 (
	input DI0, DI1,
	input WAD0, WAD1, WAD2, WAD3,
	input WRE, WCK,
	input RAD0, RAD1, RAD2, RAD3,
	output DO0, DO1
);
	parameter WCKMUX = "WCK";
	parameter WREMUX = "WRE";
	parameter INITVAL_0 = 16'h0000;
	parameter INITVAL_1 = 16'h0000;

	reg [1:0] mem[15:0];

	integer i;
	initial begin
		for (i = 0; i < 16; i = i + 1)
			mem[i] <= {INITVAL_1[i], INITVAL_0[i]};
	end

	wire muxwck = (WCKMUX == "INV") ? ~WCK : WCK;

	reg muxwre;
	always @(*)
		case (WREMUX)
			"1": muxwre = 1'b1;
			"0": muxwre = 1'b0;
			"INV": muxwre = ~WRE;
			default: muxwre = WRE;
		endcase


	always @(posedge muxwck)
		if (muxwre)
			mem[{WAD3, WAD2, WAD1, WAD0}] <= {DI1, DI0};

	assign {DO1, DO0} = mem[{RAD3, RAD2, RAD1, RAD0}];
endmodule

// ---------------------------------------
(* abc9_box, lib_whitebox *)
module PFUMX (input ALUT, BLUT, C0, output Z);
	assign Z = C0 ? ALUT : BLUT;
	specify
		(ALUT => Z) = 98;
		(BLUT => Z) = 98;
		(C0 => Z) = 151;
	endspecify
endmodule

// ---------------------------------------
module TRELLIS_DPR16X4 (
	input  [3:0] DI,
	input  [3:0] WAD,
	input        WRE,
	input        WCK,
	input  [3:0] RAD,
	output [3:0] DO
);
	parameter WCKMUX = "WCK";
	parameter WREMUX = "WRE";
	parameter [63:0] INITVAL = 64'h0000000000000000;

	reg [3:0] mem[15:0];

	integer i;
	initial begin
		for (i = 0; i < 16; i = i + 1)
			mem[i] <= {INITVAL[i+3], INITVAL[i+2], INITVAL[i+1], INITVAL[i]};
	end

	wire muxwck = (WCKMUX == "INV") ? ~WCK : WCK;

	reg muxwre;
	always @(*)
		case (WREMUX)
			"1": muxwre = 1'b1;
			"0": muxwre = 1'b0;
			"INV": muxwre = ~WRE;
			default: muxwre = WRE;
		endcase

	always @(posedge muxwck)
		if (muxwre)
			mem[WAD] <= DI;

	assign DO = mem[RAD];
endmodule

// ---------------------------------------

module DPR16X4C (
		input [3:0] DI,
		input WCK, WRE,
		input [3:0] RAD,
		input [3:0] WAD,
		output [3:0] DO
);
	// For legacy Lattice compatibility, INITIVAL is a hex
	// string rather than a numeric parameter
	parameter INITVAL = "0x0000000000000000";

	function [63:0] convert_initval;
		input [143:0] hex_initval;
		reg done;
		reg [63:0] temp;
		reg [7:0] char;
		integer i;
		begin
			done = 1'b0;
			temp = 0;
			for (i = 0; i < 16; i = i + 1) begin
				if (!done) begin
					char = hex_initval[8*i +: 8];
					if (char == "x") begin
						done = 1'b1;
					end else begin
						if (char >= "0" && char <= "9")
							temp[4*i +: 4] = char - "0";
						else if (char >= "A" && char <= "F")
							temp[4*i +: 4] = 10 + char - "A";
						else if (char >= "a" && char <= "f")
							temp[4*i +: 4] = 10 + char - "a";
					end
				end
			end
			convert_initval = temp;
		end
	endfunction

	localparam conv_initval = convert_initval(INITVAL);

	reg [3:0] ram[0:15];
	integer i;
	initial begin
		for (i = 0; i < 15; i = i + 1) begin
			ram[i] <= conv_initval[4*i +: 4];
		end
	end

	always @(posedge WCK)
		if (WRE)
			ram[WAD] <= DI;

	assign DO = ram[RAD];

endmodule

// ---------------------------------------

(* lib_whitebox *)
module LUT2(input A, B, output Z);
    parameter [3:0] INIT = 4'h0;
    wire [1:0] s1 = B ?     INIT[ 3:2] :     INIT[1:0];
    assign Z =      A ?          s1[1] :         s1[0];
endmodule

// ---------------------------------------

module TRELLIS_FF(input CLK, LSR, CE, DI, M, output reg Q);
	parameter GSR = "ENABLED";
	parameter [127:0] CEMUX = "1";
	parameter CLKMUX = "CLK";
	parameter LSRMUX = "LSR";
	parameter SRMODE = "LSR_OVER_CE";
	parameter REGSET = "RESET";
	parameter [127:0] LSRMODE = "LSR";

	wire muxce;
	generate
		case (CEMUX)
			"1": assign muxce = 1'b1;
			"0": assign muxce = 1'b0;
			"INV": assign muxce = ~CE;
			default: assign muxce = CE;
		endcase
	endgenerate

	wire muxlsr = (LSRMUX == "INV") ? ~LSR : LSR;
	wire muxclk = (CLKMUX == "INV") ? ~CLK : CLK;
	wire srval;
	generate
		if (LSRMODE == "PRLD")
			assign srval = M;
		else
			assign srval = (REGSET == "SET") ? 1'b1 : 1'b0;
	endgenerate

	initial Q = srval;

	generate
		if (SRMODE == "ASYNC") begin
			always @(posedge muxclk, posedge muxlsr)
				if (muxlsr)
					Q <= srval;
				else if (muxce)
					Q <= DI;
		end else begin
			always @(posedge muxclk)
				if (muxlsr)
					Q <= srval;
				else if (muxce)
					Q <= DI;
		end
	endgenerate
endmodule

// ---------------------------------------
(* keep *)
module TRELLIS_IO(
	inout B,
	input I,
	input T,
	output O
);
	parameter DIR = "INPUT";
	reg T_pd;
	always @(*) if (T === 1'bz) T_pd <= 1'b0; else T_pd <= T;

	generate
		if (DIR == "INPUT") begin
			assign B = 1'bz;
			assign O = B;
		end else if (DIR == "OUTPUT") begin
			assign B = T_pd ? 1'bz : I;
			assign O = 1'bx;
		end else if (DIR == "BIDIR") begin
			assign B = T_pd ? 1'bz : I;
			assign O = B;
		end else begin
			ERROR_UNKNOWN_IO_MODE error();
		end
	endgenerate

endmodule

// ---------------------------------------

module INV(input A, output Z);
	assign Z = !A;
endmodule

// ---------------------------------------

module TRELLIS_SLICE(
	input A0, B0, C0, D0,
	input A1, B1, C1, D1,
	input M0, M1,
	input FCI, FXA, FXB,

	input CLK, LSR, CE,
	input DI0, DI1,

	input WD0, WD1,
	input WAD0, WAD1, WAD2, WAD3,
	input WRE, WCK,

	output F0, Q0,
	output F1, Q1,
	output FCO, OFX0, OFX1,

	output WDO0, WDO1, WDO2, WDO3,
	output WADO0, WADO1, WADO2, WADO3
);

	parameter MODE = "LOGIC";
	parameter GSR = "ENABLED";
	parameter SRMODE = "LSR_OVER_CE";
	parameter [127:0] CEMUX = "1";
	parameter CLKMUX = "CLK";
	parameter LSRMUX = "LSR";
	parameter LUT0_INITVAL = 16'h0000;
	parameter LUT1_INITVAL = 16'h0000;
	parameter REG0_SD = "0";
	parameter REG1_SD = "0";
	parameter REG0_REGSET = "RESET";
	parameter REG1_REGSET = "RESET";
	parameter REG0_LSRMODE = "LSR";
	parameter REG1_LSRMODE = "LSR";
	parameter [127:0] CCU2_INJECT1_0 = "NO";
	parameter [127:0] CCU2_INJECT1_1 = "NO";
	parameter WREMUX = "WRE";
	parameter WCKMUX = "WCK";

	parameter A0MUX = "A0";
	parameter A1MUX = "A1";
	parameter B0MUX = "B0";
	parameter B1MUX = "B1";
	parameter C0MUX = "C0";
	parameter C1MUX = "C1";
	parameter D0MUX = "D0";
	parameter D1MUX = "D1";

	wire A0m, B0m, C0m, D0m;
	wire A1m, B1m, C1m, D1m;

	generate
		if (A0MUX == "1") assign A0m = 1'b1; else assign A0m = A0;
		if (B0MUX == "1") assign B0m = 1'b1; else assign B0m = B0;
		if (C0MUX == "1") assign C0m = 1'b1; else assign C0m = C0;
		if (D0MUX == "1") assign D0m = 1'b1; else assign D0m = D0;
		if (A1MUX == "1") assign A1m = 1'b1; else assign A1m = A1;
		if (B1MUX == "1") assign B1m = 1'b1; else assign B1m = B1;
		if (C1MUX == "1") assign C1m = 1'b1; else assign C1m = C1;
		if (D1MUX == "1") assign D1m = 1'b1; else assign D1m = D1;

	endgenerate

	function [15:0] permute_initval;
		input [15:0] initval;
		integer i;
		begin
			for (i = 0; i < 16; i = i + 1) begin
				permute_initval[{i[0], i[2], i[1], i[3]}] = initval[i];
			end
		end
	endfunction

	generate
		if (MODE == "LOGIC") begin
			// LUTs
			LUT4 #(
				.INIT(LUT0_INITVAL)
			) lut4_0 (
				.A(A0m), .B(B0m), .C(C0m), .D(D0m),
				.Z(F0)
			);
			LUT4 #(
				.INIT(LUT1_INITVAL)
			) lut4_1 (
				.A(A1m), .B(B1m), .C(C1m), .D(D1m),
				.Z(F1)
			);
			// LUT expansion muxes
			PFUMX lut5_mux (.ALUT(F1), .BLUT(F0), .C0(M0), .Z(OFX0));
			L6MUX21 lutx_mux (.D0(FXA), .D1(FXB), .SD(M1), .Z(OFX1));
		end else if (MODE == "CCU2") begin
			CCU2C #(
				.INIT0(LUT0_INITVAL),
				.INIT1(LUT1_INITVAL),
				.INJECT1_0(CCU2_INJECT1_0),
				.INJECT1_1(CCU2_INJECT1_1)
		  ) ccu2c_i (
				.CIN(FCI),
				.A0(A0m), .B0(B0m), .C0(C0m), .D0(D0m),
				.A1(A1m), .B1(B1m), .C1(C1m), .D1(D1m),
				.S0(F0), .S1(F1),
				.COUT(FCO)
			);
		end else if (MODE == "RAMW") begin
			assign WDO0 = C1m;
			assign WDO1 = A1m;
			assign WDO2 = D1m;
			assign WDO3 = B1m;
			assign WADO0 = D0m;
			assign WADO1 = B0m;
			assign WADO2 = C0m;
			assign WADO3 = A0m;
		end else if (MODE == "DPRAM") begin
			TRELLIS_RAM16X2 #(
				.INITVAL_0(permute_initval(LUT0_INITVAL)),
				.INITVAL_1(permute_initval(LUT1_INITVAL)),
				.WREMUX(WREMUX)
			) ram_i (
				.DI0(WD0), .DI1(WD1),
				.WAD0(WAD0), .WAD1(WAD1), .WAD2(WAD2), .WAD3(WAD3),
				.WRE(WRE), .WCK(WCK),
				.RAD0(D0m), .RAD1(B0m), .RAD2(C0m), .RAD3(A0m),
				.DO0(F0), .DO1(F1)
			);
			// TODO: confirm RAD and INITVAL ordering
			// DPRAM mode contract?
`ifdef FORMAL
			always @(*) begin
				assert(A0m==A1m);
				assert(B0m==B1m);
				assert(C0m==C1m);
				assert(D0m==D1m);
			end
`endif
		end else begin
			ERROR_UNKNOWN_SLICE_MODE error();
		end
	endgenerate

	// FF input selection muxes
	wire muxdi0 = (REG0_SD == "1") ? DI0 : M0;
	wire muxdi1 = (REG1_SD == "1") ? DI1 : M1;
	// Flipflops
	TRELLIS_FF #(
		.GSR(GSR),
		.CEMUX(CEMUX),
		.CLKMUX(CLKMUX),
		.LSRMUX(LSRMUX),
		.SRMODE(SRMODE),
		.REGSET(REG0_REGSET),
		.LSRMODE(REG0_LSRMODE)
	) ff_0 (
		.CLK(CLK), .LSR(LSR), .CE(CE),
		.DI(muxdi0), .M(M0),
		.Q(Q0)
	);
	TRELLIS_FF #(
		.GSR(GSR),
		.CEMUX(CEMUX),
		.CLKMUX(CLKMUX),
		.LSRMUX(LSRMUX),
		.SRMODE(SRMODE),
		.REGSET(REG1_REGSET),
		.LSRMODE(REG1_LSRMODE)
	) ff_1 (
		.CLK(CLK), .LSR(LSR), .CE(CE),
		.DI(muxdi1), .M(M1),
		.Q(Q1)
	);
endmodule

(* blackbox *)
module DP16KD(
  input DIA17, DIA16, DIA15, DIA14, DIA13, DIA12, DIA11, DIA10, DIA9, DIA8, DIA7, DIA6, DIA5, DIA4, DIA3, DIA2, DIA1, DIA0,
  input ADA13, ADA12, ADA11, ADA10, ADA9, ADA8, ADA7, ADA6, ADA5, ADA4, ADA3, ADA2, ADA1, ADA0,
  input CEA, OCEA, CLKA, WEA, RSTA,
  input CSA2, CSA1, CSA0,
  output DOA17, DOA16, DOA15, DOA14, DOA13, DOA12, DOA11, DOA10, DOA9, DOA8, DOA7, DOA6, DOA5, DOA4, DOA3, DOA2, DOA1, DOA0,

  input DIB17, DIB16, DIB15, DIB14, DIB13, DIB12, DIB11, DIB10, DIB9, DIB8, DIB7, DIB6, DIB5, DIB4, DIB3, DIB2, DIB1, DIB0,
  input ADB13, ADB12, ADB11, ADB10, ADB9, ADB8, ADB7, ADB6, ADB5, ADB4, ADB3, ADB2, ADB1, ADB0,
  input CEB, OCEB, CLKB, WEB, RSTB,
  input CSB2, CSB1, CSB0,
  output DOB17, DOB16, DOB15, DOB14, DOB13, DOB12, DOB11, DOB10, DOB9, DOB8, DOB7, DOB6, DOB5, DOB4, DOB3, DOB2, DOB1, DOB0
);
	parameter DATA_WIDTH_A = 18;
	parameter DATA_WIDTH_B = 18;

	parameter REGMODE_A = "NOREG";
	parameter REGMODE_B = "NOREG";

	parameter RESETMODE = "SYNC";
	parameter ASYNC_RESET_RELEASE = "SYNC";

	parameter CSDECODE_A = "0b000";
	parameter CSDECODE_B = "0b000";

	parameter WRITEMODE_A = "NORMAL";
	parameter WRITEMODE_B = "NORMAL";

	parameter DIA17MUX = "DIA17";
	parameter DIA16MUX = "DIA16";
	parameter DIA15MUX = "DIA15";
	parameter DIA14MUX = "DIA14";
	parameter DIA13MUX = "DIA13";
	parameter DIA12MUX = "DIA12";
	parameter DIA11MUX = "DIA11";
	parameter DIA10MUX = "DIA10";
	parameter DIA9MUX = "DIA9";
	parameter DIA8MUX = "DIA8";
	parameter DIA7MUX = "DIA7";
	parameter DIA6MUX = "DIA6";
	parameter DIA5MUX = "DIA5";
	parameter DIA4MUX = "DIA4";
	parameter DIA3MUX = "DIA3";
	parameter DIA2MUX = "DIA2";
	parameter DIA1MUX = "DIA1";
	parameter DIA0MUX = "DIA0";
	parameter ADA13MUX = "ADA13";
	parameter ADA12MUX = "ADA12";
	parameter ADA11MUX = "ADA11";
	parameter ADA10MUX = "ADA10";
	parameter ADA9MUX = "ADA9";
	parameter ADA8MUX = "ADA8";
	parameter ADA7MUX = "ADA7";
	parameter ADA6MUX = "ADA6";
	parameter ADA5MUX = "ADA5";
	parameter ADA4MUX = "ADA4";
	parameter ADA3MUX = "ADA3";
	parameter ADA2MUX = "ADA2";
	parameter ADA1MUX = "ADA1";
	parameter ADA0MUX = "ADA0";
	parameter CEAMUX = "CEA";
	parameter OCEAMUX = "OCEA";
	parameter CLKAMUX = "CLKA";
	parameter WEAMUX = "WEA";
	parameter RSTAMUX = "RSTA";
	parameter CSA2MUX = "CSA2";
	parameter CSA1MUX = "CSA1";
	parameter CSA0MUX = "CSA0";
	parameter DOA17MUX = "DOA17";
	parameter DOA16MUX = "DOA16";
	parameter DOA15MUX = "DOA15";
	parameter DOA14MUX = "DOA14";
	parameter DOA13MUX = "DOA13";
	parameter DOA12MUX = "DOA12";
	parameter DOA11MUX = "DOA11";
	parameter DOA10MUX = "DOA10";
	parameter DOA9MUX = "DOA9";
	parameter DOA8MUX = "DOA8";
	parameter DOA7MUX = "DOA7";
	parameter DOA6MUX = "DOA6";
	parameter DOA5MUX = "DOA5";
	parameter DOA4MUX = "DOA4";
	parameter DOA3MUX = "DOA3";
	parameter DOA2MUX = "DOA2";
	parameter DOA1MUX = "DOA1";
	parameter DOA0MUX = "DOA0";
	parameter DIB17MUX = "DIB17";
	parameter DIB16MUX = "DIB16";
	parameter DIB15MUX = "DIB15";
	parameter DIB14MUX = "DIB14";
	parameter DIB13MUX = "DIB13";
	parameter DIB12MUX = "DIB12";
	parameter DIB11MUX = "DIB11";
	parameter DIB10MUX = "DIB10";
	parameter DIB9MUX = "DIB9";
	parameter DIB8MUX = "DIB8";
	parameter DIB7MUX = "DIB7";
	parameter DIB6MUX = "DIB6";
	parameter DIB5MUX = "DIB5";
	parameter DIB4MUX = "DIB4";
	parameter DIB3MUX = "DIB3";
	parameter DIB2MUX = "DIB2";
	parameter DIB1MUX = "DIB1";
	parameter DIB0MUX = "DIB0";
	parameter ADB13MUX = "ADB13";
	parameter ADB12MUX = "ADB12";
	parameter ADB11MUX = "ADB11";
	parameter ADB10MUX = "ADB10";
	parameter ADB9MUX = "ADB9";
	parameter ADB8MUX = "ADB8";
	parameter ADB7MUX = "ADB7";
	parameter ADB6MUX = "ADB6";
	parameter ADB5MUX = "ADB5";
	parameter ADB4MUX = "ADB4";
	parameter ADB3MUX = "ADB3";
	parameter ADB2MUX = "ADB2";
	parameter ADB1MUX = "ADB1";
	parameter ADB0MUX = "ADB0";
	parameter CEBMUX = "CEB";
	parameter OCEBMUX = "OCEB";
	parameter CLKBMUX = "CLKB";
	parameter WEBMUX = "WEB";
	parameter RSTBMUX = "RSTB";
	parameter CSB2MUX = "CSB2";
	parameter CSB1MUX = "CSB1";
	parameter CSB0MUX = "CSB0";
	parameter DOB17MUX = "DOB17";
	parameter DOB16MUX = "DOB16";
	parameter DOB15MUX = "DOB15";
	parameter DOB14MUX = "DOB14";
	parameter DOB13MUX = "DOB13";
	parameter DOB12MUX = "DOB12";
	parameter DOB11MUX = "DOB11";
	parameter DOB10MUX = "DOB10";
	parameter DOB9MUX = "DOB9";
	parameter DOB8MUX = "DOB8";
	parameter DOB7MUX = "DOB7";
	parameter DOB6MUX = "DOB6";
	parameter DOB5MUX = "DOB5";
	parameter DOB4MUX = "DOB4";
	parameter DOB3MUX = "DOB3";
	parameter DOB2MUX = "DOB2";
	parameter DOB1MUX = "DOB1";
	parameter DOB0MUX = "DOB0";

	parameter WID = 0;

	parameter GSR = "ENABLED";

	parameter INITVAL_00 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_01 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_02 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_03 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_04 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_05 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_06 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_07 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_08 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_09 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0A = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0B = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0C = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0D = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0E = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_0F = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_10 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_11 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_12 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_13 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_14 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_15 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_16 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_17 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_18 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_19 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1A = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1B = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1C = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1D = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1E = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_1F = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_20 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_21 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_22 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_23 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_24 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_25 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_26 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_27 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_28 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_29 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2A = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2B = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2C = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2D = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2E = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_2F = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_30 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_31 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_32 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_33 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_34 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_35 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_36 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_37 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_38 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_39 = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3A = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3B = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3C = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3D = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3E = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
	parameter INITVAL_3F = 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
endmodule

`ifndef NO_INCLUDES

`include "cells_ff.vh"
`include "cells_io.vh"

`endif
