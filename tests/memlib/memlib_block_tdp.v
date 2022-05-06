module RAM_BLOCK_TDP(
	input PORT_A_CLK,
	input PORT_A_WR_EN,
	input [9:0] PORT_A_ADDR,
	input [15:0] PORT_A_WR_DATA,
	output reg [15:0] PORT_A_RD_DATA,
	input PORT_B_CLK,
	input PORT_B_WR_EN,
	input [9:0] PORT_B_ADDR,
	input [15:0] PORT_B_WR_DATA,
	output reg [15:0] PORT_B_RD_DATA
);

parameter INIT = 0;
parameter PORT_A_WIDTH = 1;
parameter PORT_B_WIDTH = 1;
parameter PORT_A_CLK_POL = 0;
parameter PORT_B_CLK_POL = 0;

reg [2**10-1:0] mem = INIT;

always @(negedge (PORT_A_CLK ^ PORT_A_CLK_POL)) begin
	if (PORT_A_WR_EN) begin
		mem[PORT_A_ADDR+:PORT_A_WIDTH] <= PORT_A_WR_DATA;
	end else begin
		PORT_A_RD_DATA <= mem[PORT_A_ADDR+:PORT_A_WIDTH];
	end
end

always @(negedge (PORT_B_CLK ^ PORT_B_CLK_POL)) begin
	if (PORT_B_WR_EN) begin
		mem[PORT_B_ADDR+:PORT_B_WIDTH] <= PORT_B_WR_DATA;
	end else begin
		PORT_B_RD_DATA <= mem[PORT_B_ADDR+:PORT_B_WIDTH];
	end
end

endmodule
