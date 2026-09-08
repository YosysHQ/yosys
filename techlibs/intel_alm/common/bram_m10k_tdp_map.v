// Equal-width, whole-word true dual-port M10K. memory_libmap addresses
// count 10-bit words, so the 20-bit configuration discards the low bit.
module \$__MISTRAL_M10K_TDP_ (PORT_A_CLK, PORT_A_CLK_EN, PORT_A_ADDR,
    PORT_A_WR_DATA, PORT_A_WR_EN, PORT_A_RD_DATA,
    PORT_B_CLK, PORT_B_CLK_EN, PORT_B_ADDR,
    PORT_B_WR_DATA, PORT_B_WR_EN, PORT_B_RD_DATA);
parameter WIDTH = 10;
parameter INIT = 0;
localparam SHIFT = $clog2(WIDTH / 10);
input PORT_A_CLK, PORT_A_CLK_EN, PORT_A_WR_EN;
input PORT_B_CLK, PORT_B_CLK_EN, PORT_B_WR_EN;
input [9:0] PORT_A_ADDR, PORT_B_ADDR;
input [WIDTH-1:0] PORT_A_WR_DATA, PORT_B_WR_DATA;
output [WIDTH-1:0] PORT_A_RD_DATA, PORT_B_RD_DATA;
MISTRAL_M10K_TDP #(.CFG_ABITS(10-SHIFT), .CFG_DBITS(WIDTH), .INIT(INIT))
    _TECHMAP_REPLACE_ (
    .CLK1(PORT_A_CLK), .CLK2(PORT_B_CLK),
    .A1EN(PORT_A_CLK_EN), .B1EN(PORT_B_CLK_EN),
    .A1WE(PORT_A_WR_EN), .B1WE(PORT_B_WR_EN),
    .A1ADDR(PORT_A_ADDR[9:SHIFT]), .B1ADDR(PORT_B_ADDR[9:SHIFT]),
    .A1DATA(PORT_A_WR_DATA), .B1DATA(PORT_B_WR_DATA),
    .A1Q(PORT_A_RD_DATA), .B1Q(PORT_B_RD_DATA));
endmodule
