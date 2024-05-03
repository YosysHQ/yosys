// Stub to invert M10K write-enable.

module \$__MISTRAL_M10K (PORT_W_CLK, PORT_W_ADDR, PORT_W_WR_DATA, PORT_W_WR_EN, PORT_R_CLK, PORT_R_ADDR, PORT_R_RD_DATA, PORT_R_RD_EN);

parameter INIT = 0;
parameter WIDTH = 10;

input PORT_W_CLK, PORT_R_CLK;
input [12:0] PORT_W_ADDR, PORT_R_ADDR;
input [WIDTH-1:0] PORT_W_WR_DATA;
input PORT_W_WR_EN, PORT_R_RD_EN;
output reg [WIDTH-1:0] PORT_R_RD_DATA;

localparam CFG_ABITS = WIDTH == 40 ? 8 : WIDTH == 20 ? 9 : WIDTH == 10 ? 10 : WIDTH == 5 ? 11 : WIDTH == 2 ? 12 : 13;

// Normal M10K configs use WREN[1], which is negative-true.
// However, 8x40-bit mode uses WREN[0], which is positive-true.
wire wren;
if (WIDTH == 40)
    assign wren = PORT_W_WR_EN;
else
    assign wren = !PORT_W_WR_EN;

MISTRAL_M10K #(.INIT(INIT), .CFG_ABITS(CFG_ABITS), .CFG_DBITS(WIDTH)) _TECHMAP_REPLACE_ (.CLK1(PORT_W_CLK), .A1ADDR(PORT_W_ADDR), .A1DATA(PORT_W_WR_DATA), .A1EN(wren), .B1ADDR(PORT_R_ADDR), .B1DATA(PORT_R_RD_DATA), .B1EN(PORT_R_RD_EN));

endmodule
