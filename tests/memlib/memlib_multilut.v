module LUT_MULTI(
	input [3:0] PORT_R0_ADDR,
	input [3:0] PORT_R1_ADDR,
	input [3:0] PORT_R2_ADDR,
	input [3:0] PORT_R3_ADDR,
	input [3:0] PORT_R4_ADDR,
	input [3:0] PORT_R5_ADDR,
	input [3:0] PORT_R6_ADDR,
	input [3:0] PORT_RW_ADDR,
	input PORT_RW_CLK,
	input PORT_RW_WR_EN,
	input [1:0] PORT_RW_WR_DATA,
	output [1:0] PORT_R0_RD_DATA,
	output [1:0] PORT_R1_RD_DATA,
	output [1:0] PORT_R2_RD_DATA,
	output [1:0] PORT_R3_RD_DATA,
	output [1:0] PORT_R4_RD_DATA,
	output [1:0] PORT_R5_RD_DATA,
	output [1:0] PORT_R6_RD_DATA,
	output [1:0] PORT_RW_RD_DATA
);

parameter INIT = 0;
parameter OPTION_PORTS = "UNDEFINED";

reg [1:0] mem [0:15];
integer i;
initial
	for (i = 0; i < 16; i += 1)
		mem[i] = INIT[i*4+:4];

assign PORT_R0_RD_DATA = mem[PORT_R0_ADDR];
assign PORT_R1_RD_DATA = mem[PORT_R1_ADDR];
assign PORT_R2_RD_DATA = mem[PORT_R2_ADDR];
assign PORT_R3_RD_DATA = mem[PORT_R3_ADDR];
assign PORT_R4_RD_DATA = mem[PORT_R4_ADDR];
assign PORT_R5_RD_DATA = mem[PORT_R5_ADDR];
assign PORT_R6_RD_DATA = mem[PORT_R6_ADDR];
assign PORT_RW_RD_DATA = mem[PORT_RW_ADDR];

always @(posedge PORT_RW_CLK)
	if (PORT_RW_WR_EN)
		mem[PORT_RW_ADDR] <= PORT_RW_WR_DATA;

endmodule
