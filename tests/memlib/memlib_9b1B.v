module RAM_9b1B 
#(
	parameter INIT = 0,
	parameter OPTION_INIT = "UNDEFINED",
	parameter PORT_R_WIDTH = 9,
	parameter PORT_W_WIDTH = 9,
	parameter PORT_R_CLK_POL = 0,
	parameter PORT_W_CLK_POL = 0,
	parameter PORT_W_WR_EN_WIDTH = 1
)
(
	input PORT_R_CLK,
	input [6:0] PORT_R_ADDR,
	output reg [PORT_R_WIDTH-1:0] PORT_R_RD_DATA,
	input PORT_W_CLK,
	input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN,
	input [6:0] PORT_W_ADDR,
	input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA
);

reg [8:0] mem [0:15];

integer i;
initial
	for (i = 0; i < 16; i += 1)
		case (OPTION_INIT)
		"NONE": mem[i] = mem[i]; //?
		"ZERO": mem[i] = 9'h0;
		"ANY": mem[i] = INIT[i*9+:9];
		"NO_UNDEF": mem[i] = INIT[i*9+:9];
		"UNDEFINED": mem[i] = 9'hx;
		endcase

wire [3:0] addr_r;
assign addr_r = PORT_R_ADDR[6:3];
reg [17:0] mem_read;
reg [2:0] subaddr_r;
always @(negedge (PORT_R_CLK ^ PORT_R_CLK_POL)) begin
	subaddr_r <= PORT_R_ADDR[2:0];
	mem_read[8:0] <= mem[addr_r];
	if (PORT_R_WIDTH == 18)
		mem_read[17:9] <= mem[addr_r + 1];
end

always @(mem_read, subaddr_r) begin
	case (PORT_R_WIDTH)
	18: PORT_R_RD_DATA <= mem_read;
	9:  PORT_R_RD_DATA <= mem_read[8:0];
	4:  PORT_R_RD_DATA <= mem_read[subaddr_r[2]*4+:4];
	2:  PORT_R_RD_DATA <= mem_read[subaddr_r[2:1]*2+:2];
	1:  PORT_R_RD_DATA <= mem_read[subaddr_r];
	endcase
end

wire [3:0] addr_w;
assign addr_w = PORT_W_ADDR[6:3];
always @(negedge (PORT_W_CLK ^ PORT_W_CLK_POL)) begin
	if (PORT_W_WR_EN[0])
		case (PORT_W_WIDTH)
		18,
		9: mem[addr_w] <= PORT_W_WR_DATA[8:0];
		4: mem[addr_w][PORT_W_ADDR[2]*4+:4] <= PORT_W_WR_DATA;
		2: mem[addr_w][PORT_W_ADDR[2:1]*2+:2] <= PORT_W_WR_DATA;
		1: mem[addr_w][PORT_W_ADDR[2:0]] <= PORT_W_WR_DATA;
		endcase
	if (PORT_W_WR_EN[1])
		mem[addr_w + 1] <= PORT_W_WR_DATA[17:9];
end

endmodule
