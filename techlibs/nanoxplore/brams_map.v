module $__NX_RAM_ (...);

parameter INIT = 0;
parameter OPTION_STD_MODE = "";

parameter WIDTH = 24;
parameter PORT_A_CLK_POL = 1;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input [15:0] PORT_A_ADDR;
input [WIDTH-1:0] PORT_A_WR_DATA;
wire [24-1:0] A_DATA;
output [WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_CLK_POL = 1;

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input [15:0] PORT_B_ADDR;
input [WIDTH-1:0] PORT_B_WR_DATA;
wire [24-1:0] B_DATA;
output [WIDTH-1:0] PORT_B_RD_DATA;

generate
    if (OPTION_STD_MODE == "NOECC_48kx1") begin
        assign A_DATA = {24{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {24{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_24kx2") begin
        assign A_DATA = {12{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {12{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_16kx3") begin
        assign A_DATA = {8{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {8{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_12kx4") begin
        assign A_DATA = {6{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {6{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_8kx6") begin
        assign A_DATA = {4{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {4{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_6kx8") begin
        assign A_DATA = {3{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {3{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_4kx12") begin
        assign A_DATA = {2{PORT_A_WR_DATA[WIDTH-1:0]}};
        assign B_DATA = {2{PORT_B_WR_DATA[WIDTH-1:0]}};
    end
    else if (OPTION_STD_MODE == "NOECC_2kx24") begin
        assign A_DATA = PORT_A_WR_DATA;
        assign B_DATA = PORT_B_WR_DATA;
    end
endgenerate

NX_RAM_WRAP #(
    .std_mode(OPTION_STD_MODE),
    .mcka_edge(PORT_A_CLK_POL == 1 ? 1'b0 : 1'b1),
    .mckb_edge(PORT_B_CLK_POL == 1 ? 1'b0 : 1'b1),
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
    .BA(B_DATA),
    .BI(PORT_B_WR_DATA),
    .BO(PORT_B_RD_DATA)
);
endmodule