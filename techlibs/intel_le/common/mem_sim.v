
// The M9K
// --------
// TODO

module MISTRAL_M9K(CLK1, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

parameter CFG_ABITS = 9;
parameter CFG_DBITS = 9;

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
