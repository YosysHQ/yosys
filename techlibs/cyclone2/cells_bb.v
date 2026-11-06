// Cyclone II primitives as nextpnr-himbaechel's cyclone2 uarch takes them.
// Blackboxes for synthesis.

(* blackbox *)
module LCELL_COMB (input DATAA, input DATAB, input DATAC, input DATAD, input CIN,
                   output COMBOUT, output COUT);
  parameter [15:0] LUT_MASK = 16'hFFFF;
endmodule

(* blackbox *)
module LCELL_FF (input DATAIN, input CLK, input ENA, input ACLR, input SCLR, output REGOUT);
endmodule

(* blackbox *)
module CY2_IBUF (input PAD, output COMBOUT);
endmodule

(* blackbox *)
module CY2_OBUF (input DATAOUT, output PAD);
endmodule
