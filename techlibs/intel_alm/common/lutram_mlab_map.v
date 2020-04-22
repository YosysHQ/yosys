module __MISTRAL_MLAB(CLK1, CLK2, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA);

parameter CFG_ABITS = 5;
parameter CFG_DBITS = 20;

input CLK1, CLK2;
input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input A1EN;
output [CFG_DBITS-1:0] B1DATA;

altsyncram #(
    .operation_mode("dual_port"),
    .ram_block_type("mlab"),
    .widthad_a(CFG_ABITS),
    .width_a(CFG_DBITS),
    .widthad_b(CFG_ABITS),
    .width_b(CFG_DBITS),
) _TECHMAP_REPLACE_ (
    .address_a(A1ADDR),
    .data_a(A1DATA),
    .wren_a(A1EN),
    .address_b(B1ADDR),
    .q_b(B1DATA),
    .clock0(CLK1),
    .clock1(CLK1),
);

endmodule
