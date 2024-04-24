module $__NX_RAM_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_A_WIDTH = 9;
parameter PORT_A_CLK_POL = 1;
parameter PORT_A_OPTION_WRITEMODE = "NORMAL";

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [12:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_WIDTH = 9;
parameter PORT_B_CLK_POL = 1;
parameter PORT_B_OPTION_WRITEMODE = "NORMAL";

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input PORT_B_RD_SRST;
input PORT_B_RD_ARST;
input [12:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;

NX_RAM_WRAP #(
) _TECHMAP_REPLACE_ (
    .ACK(PORT_A_CLK),
    .AA(PORT_A_ADDR),
    .AI(PORT_A_WR_DATA),
    .AO(PORT_A_RD_DATA),

    .BCK(PORT_B_CLK),
    .BA(PORT_B_ADDR),
    .BI(PORT_B_WR_DATA),
    .BO(PORT_B_RD_DATA)
);
endmodule