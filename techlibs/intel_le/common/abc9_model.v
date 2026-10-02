// This is a purely-synchronous flop, that ABC9 can use for sequential synthesis.
(* abc9_flop, lib_whitebox *)
module $__MISTRAL_FF_SYNCONLY (
    input DATAIN, CLK, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

MISTRAL_FF ff (.DATAIN(DATAIN), .CLK(CLK), .ENA(ENA), .ACLR(1'b1), .SCLR(SCLR), .SLOAD(SLOAD), .SDATA(SDATA), .Q(Q));

endmodule
