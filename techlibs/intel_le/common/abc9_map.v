// This file exists to map purely-synchronous flops to ABC9 flops, while 
// mapping flops with asynchronous-clear as boxes, this is because ABC9 
// doesn't support asynchronous-clear flops in sequential synthesis.

module MISTRAL_FF(
    input DATAIN, CLK, ACLR, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

parameter _TECHMAP_CONSTMSK_ACLR_ = 1'b0;

// If the async-clear is constant, we assume it's disabled.
if (_TECHMAP_CONSTMSK_ACLR_ != 1'b0)
    $__MISTRAL_FF_SYNCONLY _TECHMAP_REPLACE_ (.DATAIN(DATAIN), .CLK(CLK), .ENA(ENA), .SCLR(SCLR), .SLOAD(SLOAD), .SDATA(SDATA), .Q(Q));
else
    wire _TECHMAP_FAIL_ = 1;

endmodule
