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



// The M9K
// --------
// TODO

module MISTRAL_M9K(CLK1, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;

input CLK1;
input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input A1EN, B1EN;
output reg [CFG_DBITS-1:0] B1DATA;

reg [2**CFG_ABITS * CFG_DBITS - 1 : 0] mem = 0;

specify
    $setup(A1ADDR, posedge CLK1, 0);
    $setup(A1DATA, posedge CLK1, 0);

    if (B1EN) (posedge CLK1 => (B1DATA : A1DATA)) = 0;
endspecify

always @(posedge CLK1) begin
    if (A1EN)
        mem[(A1ADDR + 1) * CFG_DBITS - 1 : A1ADDR * CFG_DBITS] <= A1DATA;

    if (B1EN)
        B1DATA <= mem[(B1ADDR + 1) * CFG_DBITS - 1 : B1ADDR * CFG_DBITS];
end

endmodule
