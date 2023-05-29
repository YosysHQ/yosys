// The MLAB
// --------
// In addition to Logic Array Blocks (LABs) that contain ten Adaptive Logic
// Modules (ALMs, see alm_sim.v), the Cyclone V/10GX also contain
// Memory/Logic Array Blocks (MLABs) that can act as either ten ALMs, or utilise
// the memory the ALM uses to store the look-up table data for general usage,
// producing a 32 address by 20-bit block of memory. MLABs are spread out
// around the chip, so they can be placed near where they are needed, rather than
// being comparatively limited in placement for a deep but narrow memory such as
// the M10K memory block.
//
// MLABs are used mainly for shallow but wide memories, such as CPU register
// files (which have perhaps 32 registers that are comparatively wide (16/32-bit))
// or shift registers (by using the output of the Nth bit as input for the N+1th
// bit).
//
// Oddly, instead of providing a block 32 address by 20-bit cell, Quartus asks
// synthesis tools to build MLABs out of 32 address by 1-bit cells, and tries
// to put these cells in the same MLAB during cell placement. Because of this
// a MISTRAL_MLAB cell represents one of these 32 address by 1-bit cells, and
// 20 of them represent a physical MLAB.
//
// How the MLAB works
// ------------------
// MLABs are poorly documented, so the following information is based mainly
// on the simulation model and my knowledge of how memories like these work.
// Additionally, note that the ports of MISTRAL_MLAB are the ones auto-generated
// by the Yosys `memory_bram` pass, and it doesn't make sense to me to use
// `techmap` just for the sake of renaming the cell ports.
//
// The MLAB can be initialised to any value, but unfortunately Quartus only
// allows memory initialisation from a file. Since Yosys doesn't preserve input
// file information, or write the contents of an `initial` block to a file,
// Yosys can't currently initialise the MLAB in a way Quartus will accept.
//
// The MLAB takes in data from A1DATA at the rising edge of CLK1, and if A1EN
// is high, writes it to the address in A1ADDR. A1EN can therefore be used to
// conditionally write data to the MLAB.
//
// Simultaneously, the MLAB reads data from B1ADDR, and outputs it to B1DATA,
// asynchronous to CLK1 and ignoring A1EN. If a synchronous read is needed
// then the output can be fed to embedded flops. Presently, Yosys assumes
// Quartus will pack external flops into the MLAB, but this is an assumption
// that needs testing.

// The vendor sim model outputs 'x for a very short period (a few
// combinational delta cycles) after each write. This has been omitted from
// the following model because it's very difficult to trigger this in practice
// as clock cycles will be much longer than any potential blip of 'x, so the
// model can be treated as always returning a defined result.

(* abc9_box, lib_whitebox *)
module MISTRAL_MLAB(input [4:0] A1ADDR, input A1DATA, A1EN,
    (* clkbuf_sink *) input CLK1,
    input [4:0] B1ADDR, output B1DATA);

reg [31:0] mem = 32'b0;

`ifdef cyclonev
specify
    $setup(A1ADDR, posedge CLK1, 86);
    $setup(A1DATA, posedge CLK1, 86);
    $setup(A1EN, posedge CLK1, 86);

    (B1ADDR[0] => B1DATA) = 487;
    (B1ADDR[1] => B1DATA) = 475;
    (B1ADDR[2] => B1DATA) = 382;
    (B1ADDR[3] => B1DATA) = 284;
    (B1ADDR[4] => B1DATA) = 96;
endspecify
`endif
`ifdef arriav
specify
    $setup(A1ADDR, posedge CLK1, 62);
    $setup(A1DATA, posedge CLK1, 62);
    $setup(A1EN, posedge CLK1, 62);

    (B1ADDR[0] => B1DATA) = 370;
    (B1ADDR[1] => B1DATA) = 292;
    (B1ADDR[2] => B1DATA) = 218;
    (B1ADDR[3] => B1DATA) = 74;
    (B1ADDR[4] => B1DATA) = 177;
endspecify
`endif
`ifdef cyclone10gx
// TODO: Cyclone 10 GX timings; the below timings are for Cyclone V
specify
    $setup(A1ADDR, posedge CLK1, 86);
    $setup(A1DATA, posedge CLK1, 86);
    $setup(A1EN, posedge CLK1, 86);

    (B1ADDR[0] => B1DATA) = 487;
    (B1ADDR[1] => B1DATA) = 475;
    (B1ADDR[2] => B1DATA) = 382;
    (B1ADDR[3] => B1DATA) = 284;
    (B1ADDR[4] => B1DATA) = 96;
endspecify
`endif

always @(posedge CLK1)
    if (A1EN) mem[A1ADDR] <= A1DATA;

assign B1DATA = mem[B1ADDR];

endmodule

// The M10K
// --------
// TODO

module MISTRAL_M10K(CLK1, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

parameter INIT = 0;

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;

(* clkbuf_sink *) input CLK1;
input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input A1EN, B1EN;
output reg [CFG_DBITS-1:0] B1DATA;

reg [2**CFG_ABITS * CFG_DBITS - 1 : 0] mem = INIT;

`ifdef cyclonev
specify
    $setup(A1ADDR, posedge CLK1, 125);
    $setup(A1DATA, posedge CLK1, 97);
    $setup(A1EN, posedge CLK1, 140);
    $setup(B1ADDR, posedge CLK1, 125);
    $setup(B1EN, posedge CLK1, 161);

    if (B1EN) (posedge CLK1 => (B1DATA : A1DATA)) = 1004;
endspecify
`endif
`ifdef arriav
specify
    $setup(A1ADDR, posedge CLK1, 97);
    $setup(A1DATA, posedge CLK1, 74);
    $setup(A1EN, posedge CLK1, 109);
    $setup(B1ADDR, posedge CLK1, 97);
    $setup(B1EN, posedge CLK1, 126);

    if (B1EN) (posedge CLK1 => (B1DATA : A1DATA)) = 787;
endspecify
`endif

always @(posedge CLK1) begin
    if (!A1EN)
        mem[(A1ADDR + 1) * CFG_DBITS - 1 : A1ADDR * CFG_DBITS] <= A1DATA;

    if (B1EN)
        B1DATA <= mem[(B1ADDR + 1) * CFG_DBITS - 1 : B1ADDR * CFG_DBITS];
end

endmodule
