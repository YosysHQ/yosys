// ---------------------------------------

(* abc_box_id=2 *)
module \$__ABC_DPR16X4_COMB (input [3:0] A, S, output [3:0] Y);
endmodule

module \$__ABC_DPR16X4_SEQ (
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
endmodule
