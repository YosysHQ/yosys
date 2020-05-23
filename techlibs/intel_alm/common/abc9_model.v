`ifdef cyclonev
`define SYNCPATH 262
`define SYNCSETUP 522
`define COMBPATH 0
`endif
`ifdef cyclone10gx
`define SYNCPATH 219
`define SYNCSETUP 268
`define COMBPATH 0
`endif

// fallback for when a family isn't detected (e.g. when techmapping for equivalence)
`ifndef SYNCPATH
`define SYNCPATH 0
`define SYNCSETUP 0
`define COMBPATH 0
`endif

// This is a purely-synchronous flop, that ABC9 can use for sequential synthesis.
(* abc9_flop, lib_whitebox *)
module MISTRAL_FF_SYNCONLY(
    input DATAIN, CLK, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

specify
    if (ENA) (posedge CLK => (Q : DATAIN)) = `SYNCPATH;
    if (ENA) (posedge CLK => (Q : SCLR)) = `SYNCPATH;
    if (ENA) (posedge CLK => (Q : SLOAD)) = `SYNCPATH;
    if (ENA) (posedge CLK => (Q : SDATA)) = `SYNCPATH;

    $setup(DATAIN, posedge CLK, `SYNCSETUP);
    $setup(ENA, posedge CLK, `SYNCSETUP);
    $setup(SCLR, posedge CLK, `SYNCSETUP);
    $setup(SLOAD, posedge CLK, `SYNCSETUP);
    $setup(SDATA, posedge CLK, `SYNCSETUP);
endspecify

initial begin
    // Altera flops initialise to zero.
	Q = 0;
end

always @(posedge CLK) begin
    // Clock-enable
	if (ENA) begin
        // Synchronous clear
        if (SCLR) Q <= 0;
        // Synchronous load
        else if (SLOAD) Q <= SDATA;
        else Q <= DATAIN;
    end
end

endmodule
