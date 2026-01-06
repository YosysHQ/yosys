/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

// DFFs
module \$_DFFE_PN0P_ (input D, C, R, E, output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFFE_PN1P_ (input D, C, R, E, output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

// for sync set/reset registers, we can pass them into ABC9. So we need to follow the simplification idiom
// and map to intermediate cell types
module \$_SDFFCE_PN0P_ (input D, C, R, E, output Q);
	MICROCHIP_SYNC_RESET_DFF _TECHMAP_REPLACE_ (.D(D), .CLK(C), .Reset(R), .En(E), .Q(Q));
endmodule

module \$_SDFFCE_PN1P_ (input D, C, R, E, output Q);
	MICROCHIP_SYNC_SET_DFF _TECHMAP_REPLACE_ (.D(D), .CLK(C), .Set(R), .En(E), .Q(Q));
endmodule


// LATCHES

module \$_DLATCH_PN0_ (input D, R, E, output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(E), .EN(1'b1), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b1), .Q(Q));
endmodule

module \$_DLATCH_PN1_ (input D, R, E, output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(E), .EN(1'b1), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b1), .Q(Q));
endmodule

module \$_DLATCH_P_ (input D, E, output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(E), .EN(1'b1), .ALn(1'b1), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b1), .Q(Q));
endmodule

// map intermediate flops to SLE
`ifdef FINAL_MAP
module MICROCHIP_SYNC_SET_DFF(
	input D,
	input CLK,
	input Set,
	input En,
	output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(CLK), .EN(En), .ALn(1'b1), .ADn(1'b0), .SLn(Set), .SD(1'b1), .LAT(1'b0), .Q(Q));
endmodule

module MICROCHIP_SYNC_RESET_DFF(
	input D,
	input CLK,
	input Reset,
	input En,
	output Q);
	SLE _TECHMAP_REPLACE_ (.D(D), .CLK(CLK), .EN(En), .ALn(1'b1), .ADn(1'b0), .SLn(Reset), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule
`endif


// LUT

`ifndef NO_LUT
module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;

	(* force_downto *)
	input [WIDTH-1:0] A;
	output Y;

	generate
	if (WIDTH == 1) begin
		CFG1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]));
	end else
	if (WIDTH == 2) begin
		CFG2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]));
	end else
	if (WIDTH == 3) begin
		CFG3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]), .C(A[2]));
	end else
	if (WIDTH == 4) begin
		CFG4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
	end else begin
		wire _TECHMAP_FAIL_ = 1;
	end
	endgenerate
endmodule
`endif

