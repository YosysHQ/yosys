module RAM_WIDE_SP #(
	parameter [79:0] INIT = 80'hx,
	parameter PORT_A_RD_WIDTH = 1,
	parameter PORT_A_WR_WIDTH = 1,
	parameter PORT_A_WIDTH = 1,
	parameter OPTION_WIDTH_MIX = 0,
	parameter PORT_A_WR_EN_WIDTH = 1,
	parameter PORT_A_RD_SRST_VALUE = 16'hx,
	parameter RD_WIDTH = OPTION_WIDTH_MIX ? PORT_A_RD_WIDTH : PORT_A_WIDTH,
	parameter WR_WIDTH = OPTION_WIDTH_MIX ? PORT_A_WR_WIDTH : PORT_A_WIDTH
) (
	input PORT_A_CLK,
	input PORT_A_RD_EN,
	input PORT_A_RD_SRST,
	input [5:0] PORT_A_ADDR,
	output reg [RD_WIDTH-1:0] PORT_A_RD_DATA,
	input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN,
	input [WR_WIDTH-1:0] PORT_A_WR_DATA
);

reg [79:0] mem;

initial mem = INIT;

always @(posedge PORT_A_CLK)
	if (PORT_A_RD_SRST)
		PORT_A_RD_DATA <= PORT_A_RD_SRST_VALUE;
	else if (PORT_A_RD_EN)
		case (RD_WIDTH)
		1: PORT_A_RD_DATA <= mem[PORT_A_ADDR[5:2] * 5 + PORT_A_ADDR[1:0]+:1];
		2: PORT_A_RD_DATA <= mem[PORT_A_ADDR[5:2] * 5 + PORT_A_ADDR[1] * 2+:2];
		5: PORT_A_RD_DATA <= mem[PORT_A_ADDR[5:2] * 5+:5];
		10: PORT_A_RD_DATA <= mem[PORT_A_ADDR[5:3] * 10+:10];
		20: PORT_A_RD_DATA <= mem[PORT_A_ADDR[5:4] * 20+:20];
		endcase

always @(posedge PORT_A_CLK)
	case (WR_WIDTH)
	1: if (PORT_A_WR_EN) mem[PORT_A_ADDR[5:2] * 5 + PORT_A_ADDR[1:0]+:1] <= PORT_A_WR_DATA;
	2: if (PORT_A_WR_EN) mem[PORT_A_ADDR[5:2] * 5 + PORT_A_ADDR[1] * 2+:2] <= PORT_A_WR_DATA;
	5: if (PORT_A_WR_EN) mem[PORT_A_ADDR[5:2] * 5+:5] <= PORT_A_WR_DATA;
	10: begin
		if (PORT_A_WR_EN[0]) mem[PORT_A_ADDR[5:3] * 10+:5] <= PORT_A_WR_DATA[4:0];
		if (PORT_A_WR_EN[1]) mem[PORT_A_ADDR[5:3] * 10 + 5+:5] <= PORT_A_WR_DATA[9:5];
	end
	20: begin
		if (PORT_A_WR_EN[0]) mem[PORT_A_ADDR[5:4] * 20+:5] <= PORT_A_WR_DATA[4:0];
		if (PORT_A_WR_EN[1]) mem[PORT_A_ADDR[5:4] * 20 + 5+:5] <= PORT_A_WR_DATA[9:5];
		if (PORT_A_WR_EN[2]) mem[PORT_A_ADDR[5:4] * 20 + 10+:5] <= PORT_A_WR_DATA[14:10];
		if (PORT_A_WR_EN[3]) mem[PORT_A_ADDR[5:4] * 20 + 15+:5] <= PORT_A_WR_DATA[19:15];
	end
	endcase

endmodule
