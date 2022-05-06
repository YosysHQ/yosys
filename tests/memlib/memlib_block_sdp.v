module RAM_BLOCK_SDP(
	input PORT_R_CLK,
	input [9:0] PORT_R_ADDR,
	output reg [15:0] PORT_R_RD_DATA,
	input PORT_W_CLK,
	input PORT_W_WR_EN,
	input [9:0] PORT_W_ADDR,
	input [15:0] PORT_W_WR_DATA
);

parameter INIT = 0;
parameter PORT_R_WIDTH = 1;
parameter PORT_W_WIDTH = 1;
parameter PORT_R_CLK_POL = 0;
parameter PORT_W_CLK_POL = 0;

reg [2**10-1:0] mem = INIT;

always @(negedge (PORT_R_CLK ^ PORT_R_CLK_POL))
	PORT_R_RD_DATA <= mem[PORT_R_ADDR+:PORT_R_WIDTH];

always @(negedge (PORT_W_CLK ^ PORT_W_CLK_POL))
	if (PORT_W_WR_EN)
		mem[PORT_W_ADDR+:PORT_W_WIDTH] <= PORT_W_WR_DATA;

endmodule
