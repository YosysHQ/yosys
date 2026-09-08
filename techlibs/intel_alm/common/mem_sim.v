// The MLAB
// --------
// In addition to Logic Array Blocks (LABs) that contain ten Adaptive Logic
// Modules (ALMs, see alm_sim.v), the Cyclone V also contains
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
// For historical reasons a MISTRAL_MLAB cell represents a 32 address by 1-bit cell,
// and 20 of them represent a physical MLAB.
//
// How the MLAB works
// ------------------
// MLABs are poorly documented, so the following information is based mainly
// on the simulation model and my knowledge of how memories like these work.
// Additionally, note that the ports of MISTRAL_MLAB are the ones auto-generated
// by the Yosys `memory_bram` pass, and it doesn't make sense to me to use
// `techmap` just for the sake of renaming the cell ports.
//
// The MLAB can be initialised to any value.
//
// The MLAB takes in data from A1DATA at the rising edge of CLK1, and if A1EN
// is high, writes it to the address in A1ADDR. A1EN can therefore be used to
// conditionally write data to the MLAB.
//
// Simultaneously, the MLAB reads data from B1ADDR, and outputs it to B1DATA,
// asynchronous to CLK1 and ignoring A1EN. If a synchronous read is needed
// then the output can be fed to embedded flops.

// The vendor sim model outputs 'x for a very short period (a few
// combinational delta cycles) after each write. This has been omitted from
// the following model because it's very difficult to trigger this in practice
// as clock cycles will be much longer than any potential blip of 'x, so the
// model can be treated as always returning a defined result.

(* abc9_box, lib_whitebox *)
module MISTRAL_MLAB(input [4:0] A1ADDR, input A1DATA, A1EN,
    (* clkbuf_sink *) input CLK1,
    input [4:0] B1ADDR, output B1DATA);

parameter [31:0] INIT = 32'b0;

reg [31:0] mem = INIT;

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

always @(posedge CLK1)
    if (A1EN) mem[A1ADDR] <= A1DATA;

assign B1DATA = mem[B1ADDR];

endmodule

// The M10K
// --------
// TODO

module MISTRAL_M10K(CLK1, A1ADDR, A1DATA, A1EN, A1BE, B1ADDR, B1DATA, B1EN, CLK2);

parameter INIT = 0;

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;
parameter CFG_RD_ABITS = CFG_ABITS;
parameter CFG_RD_DBITS = CFG_DBITS;
parameter CFG_MIXED_WIDTH = 0;
// Preserve the original single-clock primitive when CLK2 is omitted.
parameter CFG_DUAL_CLOCK = 0;
// Byte-enable mode uses two physical M10K write lanes and an active-high
// logical write enable. The default keeps the original active-low contract.
parameter CFG_BYTE_ENABLE = 0;

(* clkbuf_sink *) input CLK1;
(* clkbuf_sink *) input CLK2;
input [CFG_ABITS-1:0] A1ADDR;
input [CFG_RD_ABITS-1:0] B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input A1EN;
input [1:0] A1BE;
input B1EN;
output reg [CFG_RD_DBITS-1:0] B1DATA;

`ifdef cyclonev
specify
    $setup(A1ADDR, posedge CLK1, 125);
    $setup(A1DATA, posedge CLK1, 97);
    $setup(A1EN, posedge CLK1, 140);
    $setup(B1ADDR, posedge CLK1 &&& !CFG_DUAL_CLOCK, 125);
    $setup(B1EN, posedge CLK1 &&& !CFG_DUAL_CLOCK, 161);
    $setup(B1ADDR, posedge CLK2 &&& (CFG_DUAL_CLOCK != 0), 125);
    $setup(B1EN, posedge CLK2 &&& (CFG_DUAL_CLOCK != 0), 161);

    if (B1EN && !CFG_DUAL_CLOCK) (posedge CLK1 => (B1DATA : {CFG_RD_DBITS{1'bx}})) = 1004;
    if (B1EN && CFG_DUAL_CLOCK) (posedge CLK2 => (B1DATA : {CFG_RD_DBITS{1'bx}})) = 1004;
endspecify
`endif

generate if (CFG_MIXED_WIDTH) begin: mixed
    // A canonical array of 10-bit words preserves low-address-first ordering
    // across different read and write widths and the memory_libmap INIT bus.
    localparam [10239:0] CONTENTS = INIT;
    reg [9:0] words [0:1023];
    integer i, w, r;
    initial for (i = 0; i < 1024; i = i + 1)
        words[i] = CONTENTS[i*10 +: 10];
    always @(posedge CLK1)
        if (A1EN)
            for (w = 0; w < CFG_DBITS/10; w = w + 1)
                words[A1ADDR*(CFG_DBITS/10)+w] <= A1DATA[w*10 +: 10];
    always @(posedge CLK2)
        if (B1EN)
            for (r = 0; r < CFG_RD_DBITS/10; r = r + 1)
                B1DATA[r*10 +: 10] <= words[B1ADDR*(CFG_RD_DBITS/10)+r];
end else begin: legacy
localparam [(1 << CFG_ABITS)*CFG_DBITS-1:0] INIT_DATA = INIT;
reg [CFG_DBITS-1:0] mem [0:(1 << CFG_ABITS)-1];
integer i;
initial
    for (i = 0; i < (1 << CFG_ABITS); i = i + 1)
        mem[i] = INIT_DATA[i * CFG_DBITS +: CFG_DBITS];

always @(posedge CLK1) begin
    if (CFG_BYTE_ENABLE) begin
        if (A1EN) begin
            if (A1BE[0]) mem[A1ADDR][(CFG_DBITS / 2 > 0 ? CFG_DBITS / 2 : CFG_DBITS)-1:0] <=
                A1DATA[(CFG_DBITS / 2 > 0 ? CFG_DBITS / 2 : CFG_DBITS)-1:0];
            if (A1BE[1]) mem[A1ADDR][CFG_DBITS-1:CFG_DBITS / 2] <=
                A1DATA[CFG_DBITS-1:CFG_DBITS / 2];
        end
    end else if (CFG_DBITS == 40 ? A1EN : !A1EN)
        mem[A1ADDR] <= A1DATA;
end

wire read_clk = CFG_DUAL_CLOCK ? CLK2 : CLK1;
always @(posedge read_clk) begin
    if (B1EN)
        B1DATA <= mem[B1ADDR];
end

end endgenerate
endmodule

// Whole-word, equal-width true dual-port M10K. Each enabled positive edge
// reads or writes its own port; a write returns NEW_DATA on that port.
// Cross-port accesses to the same address involving a write have unspecified
// hardware results. This model imposes no supported cross-port write priority.
module MISTRAL_M10K_TDP(CLK1, CLK2, A1ADDR, B1ADDR, A1DATA, B1DATA,
    A1Q, B1Q, A1EN, B1EN, A1WE, B1WE);
parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;
parameter [10239:0] INIT = 0;
(* clkbuf_sink *) input CLK1, CLK2;
input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA, B1DATA;
input A1EN, B1EN, A1WE, B1WE;
output reg [CFG_DBITS-1:0] A1Q, B1Q;
reg [CFG_DBITS-1:0] mem [0:(1 << CFG_ABITS)-1];
integer i;
initial for (i = 0; i < (1 << CFG_ABITS); i = i + 1)
    mem[i] = INIT[i*CFG_DBITS +: CFG_DBITS];
always @(posedge CLK1) if (A1EN) begin
    if (A1WE) begin
        mem[A1ADDR] <= A1DATA;
        A1Q <= A1DATA;
    end else A1Q <= mem[A1ADDR];
end
always @(posedge CLK2) if (B1EN) begin
    if (B1WE) begin
        mem[B1ADDR] <= B1DATA;
        B1Q <= B1DATA;
    end else B1Q <= mem[B1ADDR];
end
endmodule
