// ---------------------------------------

module \$__ABC_DPR16X4_COMB (input [3:0] A, S, output [3:0] Y);
    assign Y = A;
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

    TRELLIS_DPR16X4 #(
      .WCKMUX(WCKMUX), .WREMUX(WREMUX), .INITVAL(INITVAL)
    ) _TECHMAP_REPLACE_ (
      .DI(DI), .WAD(WAD), .WRE(WRE), .WCK(WCK),
      .RAD(RAD), .DO(DO)
    );
endmodule
