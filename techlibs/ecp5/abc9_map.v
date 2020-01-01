// ---------------------------------------

// Attach a (combinatorial) black-box onto the output
//   of this LUTRAM primitive to capture its
//   asynchronous read behaviour
module TRELLIS_DPR16X4 (
	(* techmap_autopurge *) input  [3:0] DI,
	(* techmap_autopurge *) input  [3:0] WAD,
	(* techmap_autopurge *) input        WRE,
	(* techmap_autopurge *) input        WCK,
	(* techmap_autopurge *) input  [3:0] RAD,
	output [3:0] DO
);
	parameter WCKMUX = "WCK";
	parameter WREMUX = "WRE";
	parameter [63:0] INITVAL = 64'h0000000000000000;
    wire [3:0] $DO;

    TRELLIS_DPR16X4 #(
      .WCKMUX(WCKMUX), .WREMUX(WREMUX), .INITVAL(INITVAL)
    ) _TECHMAP_REPLACE_ (
      .DI(DI), .WAD(WAD), .WRE(WRE), .WCK(WCK),
      .RAD(RAD), .DO($DO)
    );

    $__ABC9_DPR16X4_COMB do (.$DO($DO), .RAD(RAD), .DO(DO));
endmodule
