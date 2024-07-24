module $__NX_RAM_ (...);

parameter INIT = 0;
parameter OPTION_STD_MODE = "NOECC_24kx2";

parameter PORT_A_WIDTH = 24;
parameter PORT_B_WIDTH = 24;

parameter PORT_A_CLK_POL = 1;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input [15:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
wire [24-1:0] A_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_CLK_POL = 1;

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input [15:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
wire [24-1:0] B_DATA;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;

`include "brams_init.vh"

localparam raw_config1_val = OPTION_STD_MODE == "NOECC_48kx1" ? 16'b0000000000000000:
                             OPTION_STD_MODE == "NOECC_24kx2" ? 16'b0000001001001001:
                             OPTION_STD_MODE == "NOECC_16kx3" ? 16'b0000110110110110:
                             OPTION_STD_MODE == "NOECC_12kx4" ? 16'b0000010010010010:
                             OPTION_STD_MODE == "NOECC_8kx6"  ? 16'b0000111111111111:
                             OPTION_STD_MODE == "NOECC_6kx8"  ? 16'b0000011011011011:
                             OPTION_STD_MODE == "NOECC_4kx12" ? 16'b0000100100100100:
                             OPTION_STD_MODE == "NOECC_2kx24" ? 16'b0000101101101101:
                             16'bx;

localparam A_REPEAT  =  24 / PORT_A_WIDTH;
localparam B_REPEAT  =  24 / PORT_B_WIDTH;

assign A_DATA = {A_REPEAT{PORT_A_WR_DATA[PORT_A_WIDTH-1:0]}};
assign B_DATA = {B_REPEAT{PORT_B_WR_DATA[PORT_B_WIDTH-1:0]}};

NX_RAM_WRAP #(
    .std_mode(OPTION_STD_MODE),
    .mcka_edge(PORT_A_CLK_POL == 1 ? 1'b0 : 1'b1),
    .mckb_edge(PORT_B_CLK_POL == 1 ? 1'b0 : 1'b1),
    .pcka_edge(PORT_A_CLK_POL == 1 ? 1'b0 : 1'b1),
    .pckb_edge(PORT_B_CLK_POL == 1 ? 1'b0 : 1'b1),
    .raw_config0(4'b0000),
    .raw_config1(raw_config1_val[15:0]),
    .mem_ctxt($sformatf("%s",bram_init_to_string(INIT,A_REPEAT,PORT_A_WIDTH))),
) _TECHMAP_REPLACE_ (
    .ACK(PORT_A_CLK),
    //.ACKS(PORT_A_CLK),
    //.ACKD(), // Not used in Non-ECC modes
    //.ACKR(),
    //.AR(),
    //.ACOR(),
    //.AERR(),
    .ACS(PORT_A_CLK_EN),
    .AWE(PORT_A_WR_EN),

    .AA(PORT_A_ADDR),
    .AI(A_DATA),
    .AO(PORT_A_RD_DATA),

    .BCK(PORT_B_CLK),
    //.BCKC(PORT_B_CLK),
    //.BCKD(), // Not used in Non-ECC modes
    //.BCKR()
    //.BR(),
    //.BCOR(),
    //.BERR(),
    .BCS(PORT_B_CLK_EN),
    .BWE(PORT_B_WR_EN),
    .BA(PORT_B_ADDR),
    .BI(B_DATA),
    .BO(PORT_B_RD_DATA)
);
endmodule
