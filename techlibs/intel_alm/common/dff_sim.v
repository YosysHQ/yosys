// The four D flip-flops (DFFs) in a Cyclone V/10GX Adaptive Logic Module (ALM)
// act as one-bit memory cells that can be placed very flexibly (wherever there's
// an ALM); each flop is represented by a MISTRAL_FF cell.
//
// The flops in these chips are rather flexible in some ways, but in practice
// quite crippled by FPGA standards.
//
// What the flops can do
// ---------------------
// The core flop acts as a single-bit memory that initialises to zero at chip
// reset. It takes in data on the rising edge of CLK if ENA is high,
// and outputs it to Q. The ENA (clock enable) pin can therefore be used to
// capture the input only if a condition is true.
//
// The data itself is zero if SCLR (synchronous clear) is high, else it comes
// from SDATA (synchronous data) if SLOAD (synchronous load) is high, or DATAIN
// if SLOAD is low.
//
// If ACLR (asynchronous clear) is low then Q is forced to zero, regardless of
// the synchronous inputs or CLK edge. This is most often used for an FPGA-wide
// power-on reset.
//
// An asynchronous set that sets Q to one can be emulated by inverting the input
// and output of the flop, resulting in ACLR forcing Q to zero, which then gets
// inverted to produce one. Likewise, logic can operate on the falling edge of
// CLK if CLK is inverted before being passed as an input.
//
// What the flops *can't* do
// -------------------------
// The trickiest part of the above capabilities is the lack of configurable
// initialisation state. For example, it isn't possible to implement a flop with
// asynchronous clear that initialises to one, because the hardware initialises
// to zero. Likewise, you can't emulate a flop with asynchronous set that
// initialises to zero, because the inverters mean the flop initialises to one.
//
// If the input design requires one of these cells (which appears to be rare
// in practice) then synth_intel_alm will fail to synthesize the design where
// other Yosys synthesis scripts might succeed.
//
// This stands in notable contrast to e.g. Xilinx flip-flops, which have
// configurable initialisation state and native synchronous/asynchronous
// set/clear (although not at the same time), which means they can generally
// implement a much wider variety of logic.

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

(* abc9_box, lib_whitebox *)
module MISTRAL_FF(
    input DATAIN,
    (* clkbuf_sink *) input CLK,
    input ACLR, ENA, SCLR, SLOAD, SDATA,
    output reg Q
);

`ifdef cyclonev
specify
    if (ENA && ACLR !== 1'b0 && !SCLR && !SLOAD) (posedge CLK => (Q : DATAIN)) = 731;
    if (ENA && SCLR) (posedge CLK => (Q : 1'b0)) = 890;
    if (ENA && !SCLR && SLOAD) (posedge CLK => (Q : SDATA)) = 618;

    $setup(DATAIN, posedge CLK, /* -196 */ 0);
    $setup(ENA, posedge CLK, /* -196 */ 0);
    $setup(SCLR, posedge CLK, /* -196 */ 0);
    $setup(SLOAD, posedge CLK, /* -196 */ 0);
    $setup(SDATA, posedge CLK, /* -196 */ 0);

    if (ACLR === 1'b0) (ACLR => Q) = 282;
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
