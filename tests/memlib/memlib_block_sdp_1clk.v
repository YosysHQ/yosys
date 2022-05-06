module RAM_BLOCK_SDP_1CLK(
	input CLK_C,
	input PORT_R_CLK,
	input [9:0] PORT_R_ADDR,
	output reg [15:0] PORT_R_RD_DATA,
	input PORT_W_CLK,
	input PORT_W_WR_EN,
	input [9:0] PORT_W_ADDR,
	input [15:0] PORT_W_WR_DATA
);

parameter PORT_R_CLK_POL = 0;
parameter PORT_W_CLK_POL = 0;
parameter CLK_C_POL = 0;
parameter INIT = 0;
parameter OPTION_TRANS = 2;
parameter PORT_R_WIDTH = 1;
parameter PORT_W_WIDTH = 1;

reg [2**10-1:0] mem = INIT;

always @(negedge (CLK_C ^ CLK_C_POL)) begin
	if (OPTION_TRANS == 0)
		PORT_R_RD_DATA <= mem[PORT_R_ADDR+:PORT_R_WIDTH];
	if (PORT_W_WR_EN)
		mem[PORT_W_ADDR+:PORT_W_WIDTH] = 16'hx;
	if (OPTION_TRANS == 2)
		PORT_R_RD_DATA <= mem[PORT_R_ADDR+:PORT_R_WIDTH];
	if (PORT_W_WR_EN)
		mem[PORT_W_ADDR+:PORT_W_WIDTH] = PORT_W_WR_DATA;
	if (OPTION_TRANS == 1)
		PORT_R_RD_DATA <= mem[PORT_R_ADDR+:PORT_R_WIDTH];
end


endmodule
