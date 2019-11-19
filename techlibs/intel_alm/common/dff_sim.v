// DATAIN: synchronous data input
// CLK: clock input (positive edge)
// ACLR: asynchronous clear (negative-true)
// ENA: clock-enable
// SCLR: synchronous clear
// SLOAD: synchronous load
// SDATA: synchronous load data
//
// Q: data output
//
// Note: the DFFEAS primitive is mostly emulated; it does not reflect what the hardware implements.
module MISTRAL_FF(
    input DATAIN, CLK, ACLR, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

`ifdef cyclonev
specify
    (posedge CLK => (Q : DATAIN)) = 262;
    $setup(DATAIN, posedge CLK, 522);
endspecify
`endif
`ifdef cyclone10gx
specify
    (posedge CLK => (Q : DATAIN)) = 219;
    $setup(DATAIN, posedge CLK, 268);
endspecify
`endif

initial begin
    // Altera flops initialise to zero.
	Q = 0;
end

always @(posedge CLK, negedge ACLR) begin
    // Asynchronous clear
    if (!ACLR) Q <= 0;
    // Clock-enable
	else if (ENA) begin
        // Synchronous clear
        if (SCLR) Q <= 0;
        // Synchronous load
        else if (SLOAD) Q <= SDATA;
        else Q <= DATAIN;
    end
end

endmodule
