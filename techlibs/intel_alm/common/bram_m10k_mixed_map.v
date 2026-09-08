// Explicit mixed-width SDP inference. Addresses from memory_libmap are in
// units of the narrowest (10-bit) word; wider ports have zero low bits.
module \$__MISTRAL_M10K_MIXED_ (PORT_W_CLK, PORT_W_ADDR, PORT_W_WR_DATA,
    PORT_W_WR_EN, PORT_R_CLK, PORT_R_ADDR, PORT_R_RD_DATA, PORT_R_RD_EN);
parameter PORT_W_WIDTH = 10;
parameter PORT_R_WIDTH = 40;
parameter INIT = 0;
localparam WSHIFT = $clog2(PORT_W_WIDTH / 10);
localparam RSHIFT = $clog2(PORT_R_WIDTH / 10);
input PORT_W_CLK, PORT_R_CLK, PORT_W_WR_EN, PORT_R_RD_EN;
input [9:0] PORT_W_ADDR, PORT_R_ADDR;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;
MISTRAL_M10K #(.CFG_ABITS(10-WSHIFT), .CFG_DBITS(PORT_W_WIDTH),
    .CFG_RD_ABITS(10-RSHIFT), .CFG_RD_DBITS(PORT_R_WIDTH),
    .CFG_MIXED_WIDTH(1), .CFG_DUAL_CLOCK(1), .INIT(INIT)) _TECHMAP_REPLACE_ (
    .CLK1(PORT_W_CLK), .CLK2(PORT_R_CLK), .A1EN(PORT_W_WR_EN),
    .A1ADDR(PORT_W_ADDR[9:WSHIFT]), .A1DATA(PORT_W_WR_DATA),
    .B1EN(PORT_R_RD_EN), .B1ADDR(PORT_R_ADDR[9:RSHIFT]), .B1DATA(PORT_R_RD_DATA));
endmodule
