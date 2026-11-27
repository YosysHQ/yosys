// Simulation models of the cells in cells_bb.v.

// COMBOUT is a LUT4 over (DATAA, DATAB, C, DATAD), COUT the same LUT with
// C = CIN and DATAD = 0. The hardware takes C from CIN when the carry chain
// is connected and from DATAC otherwise. The maps tie whichever one is
// unused to 1, so DATAC & CIN picks the right one.
module LCELL_COMB (input DATAA, input DATAB, input DATAC, input DATAD, input CIN,
                   output COMBOUT, output COUT);
  parameter [15:0] LUT_MASK = 16'hFFFF;
  assign COMBOUT = LUT_MASK[{DATAD, DATAC & CIN, DATAB, DATAA}];
  assign COUT = LUT_MASK[{1'b0, CIN, DATAB, DATAA}];
endmodule

// Powers up 0. ENA gates SCLR: only an enabled clock edge clears.
module LCELL_FF (input DATAIN, input CLK, input ENA, input ACLR, input SCLR,
                 output reg REGOUT);
  initial REGOUT = 1'b0;
  always @(posedge CLK, posedge ACLR)
    if (ACLR)
      REGOUT <= 1'b0;
    else if (ENA)
      REGOUT <= SCLR ? 1'b0 : DATAIN;
endmodule

module CY2_IBUF (input PAD, output COMBOUT);
  assign COMBOUT = PAD;
endmodule

module CY2_OBUF (input DATAOUT, output PAD);
  assign PAD = DATAOUT;
endmodule
