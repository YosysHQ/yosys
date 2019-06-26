// ---------------------------------------

module LUT4(input A, B, C, D, output Z);
    parameter [15:0] INIT = 16'h0000;
    wire [7:0] s3 = D ?     INIT[15:8] :     INIT[7:0];
    wire [3:0] s2 = C ?       s3[ 7:4] :       s3[3:0];
    wire [1:0] s1 = B ?       s2[ 3:2] :       s2[1:0];
    assign Z =      A ?          s1[1] :         s1[0];
endmodule

// ---------------------------------------

module L6MUX21 (input D0, D1, SD, output Z);
	assign Z = SD ? D1 : D0;
endmodule

// ---------------------------------------

module CCU2C(input CIN, A0, B0, C0, D0, A1, B1, C1, D1,
	           output S0, S1, COUT);

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

module PFUMX (input ALUT, BLUT, C0, output Z);
	assign Z = C0 ? ALUT : BLUT;
endmodule

// ---------------------------------------

module TRELLIS_DPR16X4 (
	input [3:0] DI,
	input [3:0] WAD,
	input WRE, WCK,
	input [3:0] RAD,
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

	reg muxce;
	always @(*)
		case (CEMUX)
			"1": muxce = 1'b1;
			"0": muxce = 1'b0;
			"INV": muxce = ~CE;
			default: muxce = CE;
		endcase

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
				.A(A0), .B(B0), .C(C0), .D(D0),
				.Z(F0)
			);
			LUT4 #(
				.INIT(LUT1_INITVAL)
			) lut4_1 (
				.A(A1), .B(B1), .C(C1), .D(D1),
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
				.A0(A0), .B0(B0), .C0(C0), .D0(D0),
				.A1(A1), .B1(B1), .C1(C1), .D1(D1),
				.S0(F0), .S1(F1),
				.COUT(FCO)
			);
		end else if (MODE == "RAMW") begin
			assign WDO0 = C1;
			assign WDO1 = A1;
			assign WDO2 = D1;
			assign WDO3 = B1;
			assign WADO0 = D0;
			assign WADO1 = B0;
			assign WADO2 = C0;
			assign WADO3 = A0;
		end else if (MODE == "DPRAM") begin
			TRELLIS_RAM16X2 #(
				.INITVAL_0(permute_initval(LUT0_INITVAL)),
				.INITVAL_1(permute_initval(LUT1_INITVAL)),
				.WREMUX(WREMUX)
			) ram_i (
				.DI0(WD0), .DI1(WD1),
				.WAD0(WAD0), .WAD1(WAD1), .WAD2(WAD2), .WAD3(WAD3),
				.WRE(WRE), .WCK(WCK),
				.RAD0(D0), .RAD1(B0), .RAD2(C0), .RAD3(A0),
				.DO0(F0), .DO1(F1)
			);
			// TODO: confirm RAD and INITVAL ordering
			// DPRAM mode contract?
			always @(*) begin
				assert(A0==A1);
				assert(B0==B1);
				assert(C0==C1);
				assert(D0==D1);
			end
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

  parameter CLKAMUX = "CLKA";
  parameter CLKBMUX = "CLKB";

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

// TODO: Diamond flip-flops
// module FD1P3AX(); endmodule
// module FD1P3AY(); endmodule
// module FD1P3BX(); endmodule
// module FD1P3DX(); endmodule
// module FD1P3IX(); endmodule
// module FD1P3JX(); endmodule
// module FD1S3AX(); endmodule
// module FD1S3AY(); endmodule
module FD1S3BX(input PD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  tff (.CLK(CK), .LSR(PD), .DI(D), .Q(Q)); endmodule
module FD1S3DX(input CD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  tff (.CLK(CK), .LSR(CD), .DI(D), .Q(Q)); endmodule
module FD1S3IX(input CD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(CK), .LSR(CD), .DI(D), .Q(Q)); endmodule
module FD1S3JX(input PD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(CK), .LSR(PD), .DI(D), .Q(Q)); endmodule
// module FL1P3AY(); endmodule
// module FL1P3AZ(); endmodule
// module FL1P3BX(); endmodule
// module FL1P3DX(); endmodule
// module FL1P3IY(); endmodule
// module FL1P3JY(); endmodule
// module FL1S3AX(); endmodule
// module FL1S3AY(); endmodule

// Diamond I/O buffers
module IB   (input I, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("INPUT")) tio (.B(I), .O(O)); endmodule
module IBPU (input I, output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("INPUT"))   tio (.B(I), .O(O)); endmodule
module IBPD (input I, output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("INPUT")) tio (.B(I), .O(O)); endmodule
module OB   (input I, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) tio (.B(O), .I(I)); endmodule
module OBZ  (input I, T, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) tio (.B(O), .I(I), .T(T)); endmodule
module OBZPU(input I, T, output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("OUTPUT"))   tio (.B(O), .I(I), .T(T)); endmodule
module OBZPD(input I, T, output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("OUTPUT")) tio (.B(O), .I(I), .T(T)); endmodule
module OBCO (input I, output OT, OC); OLVDS olvds (.A(I), .Z(OT), .ZN(OC)); endmodule
module BB   (input I, T, output O, inout B); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("BIDIR")) tio (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPU (input I, T, output O, inout B); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("BIDIR"))   tio (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPD (input I, T, output O, inout B); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("BIDIR")) tio (.B(B), .I(I), .O(O), .T(T)); endmodule
module ILVDS(input A, AN, output Z); TRELLIS_IO #(.DIR("INPUT"))  tio (.B(A), .O(Z)); endmodule
module OLVDS(input A, output Z, ZN); TRELLIS_IO #(.DIR("OUTPUT")) tio (.B(Z), .I(A)); endmodule

// Diamond I/O registers
module IFS1P3BX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  tff (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3DX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  tff (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3IX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3JX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

module OFS1P3BX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  tff (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3DX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  tff (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3IX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3JX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  tff (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

// TODO: Diamond I/O latches
// module IFS1S1B(input PD, D, SCLK, output Q); endmodule
// module IFS1S1D(input CD, D, SCLK, output Q); endmodule
// module IFS1S1I(input PD, D, SCLK, output Q); endmodule
// module IFS1S1J(input CD, D, SCLK, output Q); endmodule
