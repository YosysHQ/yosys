module LUT4 #(
	parameter [15:0] INIT = 0
) (
	input A, B, C, D,
	output Z
);
	// This form of LUT propagates as few x's as possible.
	wire [7:0] s3 = D ?     INIT[15:8] :     INIT[7:0];
	wire [3:0] s2 = C ?       s3[ 7:4] :       s3[3:0];
	wire [1:0] s1 = B ?       s2[ 3:2] :       s2[1:0];
	assign Z =      A ?          s1[1] :         s1[0];
endmodule

module FACADE_FF #(
	parameter GSR = "ENABLED",
	parameter CEMUX = "1",
	parameter CLKMUX = "0",
	parameter LSRMUX = "LSR",
	parameter LSRONMUX = "LSRMUX",
	parameter SRMODE = "LSR_OVER_CE",
	parameter REGSET = "SET",
	parameter REGMODE = "FF"
) (
	input CLK, DI, LSR, CE,
	output reg Q
);

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
	wire muxlsron = (LSRONMUX == "LSRMUX") ? muxlsr : 1'b0;
	wire muxclk = (CLKMUX == "INV") ? ~CLK : CLK;
	wire srval = (REGSET == "SET") ? 1'b1 : 1'b0;

	initial Q = srval;

	generate
		if (REGMODE == "FF") begin
			if (SRMODE == "ASYNC") begin
				always @(posedge muxclk, posedge muxlsron)
					if (muxlsron)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end else begin
				always @(posedge muxclk)
					if (muxlsron)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end
		end else if (REGMODE == "LATCH") begin
			ERROR_UNSUPPORTED_FF_MODE error();
		end else begin
			ERROR_UNKNOWN_FF_MODE error();
		end
	endgenerate
endmodule

/* For consistency with ECP5; represents F0/F1 => OFX0 mux in a slice. */
module PFUMX (input ALUT, BLUT, C0, output Z);
	assign Z = C0 ? ALUT : BLUT;
endmodule

/* For consistency with ECP5; represents FXA/FXB => OFX1 mux in a slice. */
module L6MUX21 (input D0, D1, SD, output Z);
	assign Z = SD ? D1 : D0;
endmodule

/* For consistency, input order matches TRELLIS_SLICE even though the BELs in
prjtrellis were filled in clockwise order from bottom left. */
module FACADE_SLICE #(
	parameter MODE = "LOGIC",
	parameter GSR = "ENABLED",
	parameter SRMODE = "LSR_OVER_CE",
	parameter CEMUX = "1",
	parameter CLKMUX = "0",
	parameter LSRMUX = "LSR",
	parameter LSRONMUX = "LSRMUX",
	parameter LUT0_INITVAL = 16'hFFFF,
	parameter LUT1_INITVAL = 16'hFFFF,
	parameter REGMODE = "FF",
	parameter REG0_SD = "1",
	parameter REG1_SD = "1",
	parameter REG0_REGSET = "SET",
	parameter REG1_REGSET = "SET",
	parameter CCU2_INJECT1_0 = "YES",
	parameter CCU2_INJECT1_1 = "YES",
	parameter WREMUX = "INV"
) (
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

	generate
		if (MODE == "LOGIC") begin
			L6MUX21 FXMUX (.D0(FXA), .D1(FXB), .SD(M1), .Z(OFX1));

			wire k0;
			wire k1;
			PFUMX K0K1MUX (.ALUT(k1), .BLUT(k0), .C0(M0), .Z(OFX0));

			LUT4 #(.INIT(LUT0_INITVAL)) LUT_0 (.A(A0), .B(B0), .C(C0), .D(D0), .Z(k0));
			LUT4 #(.INIT(LUT1_INITVAL)) LUT_1 (.A(A0), .B(B0), .C(C0), .D(D0), .Z(k1));

			assign F0 = k0;
			assign F1 = k1;
		end else if (MODE == "CCU2") begin
			ERROR_UNSUPPORTED_SLICE_MODE error();
		end else if (MODE == "DPRAM") begin
			ERROR_UNSUPPORTED_SLICE_MODE error();
		end else begin
			ERROR_UNKNOWN_SLICE_MODE error();
		end
	endgenerate

	/* Reg can be fed either by M, or DI inputs; DI inputs muxes OFX and F
	outputs (in other words, feeds back into FACADE_SLICE). */
	wire di0 = (REG0_SD == "1") ? DI0 : M0;
	wire di1 = (REG1_SD == "1") ? DI1 : M1;

	FACADE_FF#(.GSR(GSR), .CEMUX(CEMUX), .CLKMUX(CLKMUX), .LSRMUX(LSRMUX),
		.LSRONMUX(LSRONMUX), .SRMODE(SRMODE), .REGSET(REG0_REGSET),
		.REGMODE(REGMODE)) REG_0 (.CLK(CLK), .DI(di0), .LSR(LSR), .CE(CE), .Q(Q0));
	FACADE_FF#(.GSR(GSR), .CEMUX(CEMUX), .CLKMUX(CLKMUX), .LSRMUX(LSRMUX),
		.LSRONMUX(LSRONMUX), .SRMODE(SRMODE), .REGSET(REG1_REGSET),
		.REGMODE(REGMODE)) REG_1 (.CLK(CLK), .DI(di1), .LSR(LSR), .CE(CE), .Q(Q1));
endmodule

module FACADE_IO #(
	parameter DIR = "INPUT"
) (
	inout PAD,
	input I, T,
	output O
);
	generate
		if (DIR == "INPUT") begin
			assign O = PAD;
		end else if (DIR == "OUTPUT") begin
			assign PAD = T ? 1'bz : I;
		end else if (DIR == "BIDIR") begin
			assign PAD = T ? 1'bz : I;
			assign O = PAD;
		end else begin
			ERROR_UNKNOWN_IO_MODE error();
		end
	endgenerate
endmodule

(* blackbox *)
module OSCH #(
	parameter NOM_FREQ = "2.08"
) (
	input STDBY,
	output OSC,
	output SEDSTDBY
);
endmodule

(* blackbox *)
module DCCA (
	input CLKI,
	input CE,
	output CLKO
);
endmodule

(* blackbox *)
module DCMA (
	input CLK0,
	input CLK1,
	input SEL,
	output DCMOUT
);
endmodule

// IO- "$__" cells for the iopadmap pass. These are temporary cells not meant
// to be instantiated by the end user. They are required in this file for
// attrmvcp to work.
(* blackbox *)
module  \$__FACADE_OUTPAD (input I, output O); endmodule
(* blackbox *)
module  \$__FACADE_INPAD (input I, output O); endmodule
(* blackbox *)
module  \$__FACADE_TOUTPAD (input I, OE, output O); endmodule
(* blackbox *)
module  \$__FACADE_TINOUTPAD (input I, OE, output O, inout B); endmodule
