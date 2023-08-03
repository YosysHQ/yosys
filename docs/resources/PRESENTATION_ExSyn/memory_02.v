module test(
    input             WR1_CLK,  WR2_CLK,
    input             WR1_WEN,  WR2_WEN,
    input      [7:0]  WR1_ADDR, WR2_ADDR,
    input      [7:0]  WR1_DATA, WR2_DATA,
    input             RD1_CLK,  RD2_CLK,
    input      [7:0]  RD1_ADDR, RD2_ADDR,
    output reg [7:0]  RD1_DATA, RD2_DATA
);

reg [7:0] memory [0:255];

always @(posedge WR1_CLK)
    if (WR1_WEN)
        memory[WR1_ADDR] <= WR1_DATA;

always @(posedge WR2_CLK)
    if (WR2_WEN)
        memory[WR2_ADDR] <= WR2_DATA;

always @(posedge RD1_CLK)
    RD1_DATA <= memory[RD1_ADDR];

always @(posedge RD2_CLK)
    RD2_DATA <= memory[RD2_ADDR];

endmodule
