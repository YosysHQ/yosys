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
(* abc9_box, lib_whitebox *)
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
			mem[i] <= INITVAL[4*i +: 4];
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

	specify
		// TODO
		(RAD *> DO) = 0;
	endspecify
endmodule

// ---------------------------------------

(* abc9_box, lib_whitebox *)
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

	specify
		// TODO
		(RAD *> DO) = 0;
	endspecify
endmodule

// ---------------------------------------

(* lib_whitebox *)
module LUT2(input A, B, output Z);
    parameter [3:0] INIT = 4'h0;
    wire [1:0] s1 = B ?     INIT[ 3:2] :     INIT[1:0];
    assign Z =      A ?          s1[1] :         s1[0];
endmodule

// ---------------------------------------

`ifdef YOSYS
(* abc9_flop=(SRMODE != "ASYNC"), abc9_box=(SRMODE == "ASYNC"), lib_whitebox *)
`endif
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

	specify
		$setup(DI, negedge CLK &&& CLKMUX == "INV", 0);
		$setup(CE, negedge CLK &&& CLKMUX == "INV", 0);
		$setup(LSR, negedge CLK &&& CLKMUX == "INV", 0);
		$setup(DI, posedge CLK &&& CLKMUX != "INV", 0);
		$setup(CE, posedge CLK &&& CLKMUX != "INV", 0);
		$setup(LSR, posedge CLK &&& CLKMUX != "INV", 0);
`ifndef YOSYS
		if (SRMODE == "ASYNC" && muxlsr && CLKMUX == "INV") (negedge CLK => (Q : srval)) = 0;
		if (SRMODE == "ASYNC" && muxlsr && CLKMUX != "INV") (posedge CLK => (Q : srval)) = 0;
`else
		if (SRMODE == "ASYNC" && muxlsr) (LSR => Q) = 0; 	// Technically, this should be an edge sensitive path
									// but for facilitating a bypass box, let's pretend it's
									// a simple path
`endif
		if (!muxlsr && muxce && CLKMUX == "INV") (negedge CLK => (Q : DI)) = 0;
		if (!muxlsr && muxce && CLKMUX != "INV") (posedge CLK => (Q : DI)) = 0;
	endspecify
endmodule

// ---------------------------------------
(* keep *)
module TRELLIS_IO(
	(* iopad_external_pin *)
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

module TRELLIS_COMB(
	input A, B, C, D, M,
	input FCI, F1, FXA, FXB,
	input WD,
	input WAD0, WAD1, WAD2, WAD3,
	input WRE, WCK,
	output F, FCO, OFX
);
	parameter MODE = "LOGIC";
	parameter INITVAL = 16'h0;
	parameter CCU2_INJECT1 = "NO";
	parameter WREMUX = "WRE";
	parameter IS_Z1 = 1'b0;

	generate
		if (MODE == "LOGIC") begin: mode_logic
			LUT4 #(.INIT(INITVAL)) lut4 (.A(A), .B(B), .C(C), .D(D), .Z(F));
		end else if (MODE == "CCU2") begin: mode_ccu2
			wire l4o, l2o;
			LUT4 #(.INIT(INITVAL)) lut4_0(.A(A), .B(B), .C(C), .D(D), .Z(l4o));
			LUT2 #(.INIT(INITVAL[3:0])) lut2_0(.A(A), .B(B), .Z(l2o));
			wire gated_cin_0 = (CCU2_INJECT1 == "YES") ? 1'b0 : FCI;
			assign F = l4o ^ gated_cin_0;
			wire gated_lut2_0 = (CCU2_INJECT1 == "YES") ? 1'b0 : l2o;
			wire FCO = (~l4o & gated_lut2_0) | (l4o & FCI);
		end else if (MODE == "DPRAM") begin: mode_dpram
			reg [15:0] ram = INITVAL;
			always @(posedge WCK)
				if (WRE)
					ram[{WAD3, WAD2, WAD1, WAD0}] <= WD;
			assign F = ram[{A, C, B, D}];
		end else begin
			$error("unsupported COMB mode %s", MODE);
		end

 		if (IS_Z1)
			L6MUX21 lutx_mux (.D0(FXA), .D1(FXB), .SD(M), .Z(OFX));
		else
			PFUMX lut5_mux (.ALUT(F1), .BLUT(F), .C0(M), .Z(OFX));
	endgenerate

endmodule

// Constants
module VLO(output Z);
	assign Z = 1'b0;
endmodule

module VHI(output Z);
	assign Z = 1'b1;
endmodule

`ifndef NO_INCLUDES

`include "cells_ff.vh"
`include "cells_io.vh"

`endif
