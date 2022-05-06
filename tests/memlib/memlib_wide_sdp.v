module RAM_WIDE_SDP #(
	parameter [79:0] INIT = 80'hx,
	parameter PORT_R_WIDTH = 1,
	parameter PORT_W_WIDTH = 1,
	parameter PORT_W_WR_BE_WIDTH = 1,
	parameter PORT_R_RD_SRST_VALUE = 16'hx
) (
	input PORT_R_CLK,
	input PORT_R_RD_EN,
	input PORT_R_RD_SRST,
	input [5:0] PORT_R_ADDR,
	output reg [PORT_R_WIDTH-1:0] PORT_R_RD_DATA,
	input PORT_W_CLK,
	input PORT_W_WR_EN,
	input [PORT_W_WR_BE_WIDTH-1:0] PORT_W_WR_BE,
	input [5:0] PORT_W_ADDR,
	input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA
);

reg [79:0] mem;

initial mem = INIT;

always @(posedge PORT_R_CLK)
	if (PORT_R_RD_SRST)
		PORT_R_RD_DATA <= PORT_R_RD_SRST_VALUE;
	else if (PORT_R_RD_EN)
		PORT_R_RD_DATA <= mem[PORT_R_ADDR[5:2] * 5 + PORT_R_ADDR[1:0]+:PORT_R_WIDTH];

generate
	if (PORT_W_WIDTH < 5) begin
		always @(posedge PORT_W_CLK)
			if (PORT_W_WR_EN && PORT_W_WR_BE[0])
				mem[PORT_W_ADDR[5:2] * 5 + PORT_W_ADDR[1:0]+:PORT_W_WIDTH] <= PORT_W_WR_DATA;
	end else begin
		integer i;
		always @(posedge PORT_W_CLK)
			if (PORT_W_WR_EN)
				for (i = 0; i < PORT_W_WR_BE_WIDTH; i = i + 1)
					if (PORT_W_WR_BE[i])
						mem[(PORT_W_ADDR[5:2] + i) * 5+:5] <= PORT_W_WR_DATA[i * 5+:5];
	end
endgenerate

endmodule
