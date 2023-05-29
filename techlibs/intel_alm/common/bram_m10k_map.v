// Stub to invert M10K write-enable.

module \$__MISTRAL_M10K (CLK1, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

parameter INIT = 0;

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;

input CLK1;
input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input A1EN, B1EN;
output reg [CFG_DBITS-1:0] B1DATA;

// Normal M10K configs use WREN[1], which is negative-true.
// However, 8x40-bit mode uses WREN[0], which is positive-true.
wire a1en;
if (CFG_DBITS == 40)
    assign a1en = A1EN;
else
    assign a1en = !A1EN;

MISTRAL_M10K #(.INIT(INIT), .CFG_ABITS(CFG_ABITS), .CFG_DBITS(CFG_DBITS)) _TECHMAP_REPLACE_ (.CLK1(CLK1), .A1ADDR(A1ADDR), .A1DATA(A1DATA), .A1EN(a1en), .B1ADDR(B1ADDR), .B1DATA(B1DATA), .B1EN(B1EN));

endmodule
