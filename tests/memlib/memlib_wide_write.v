module RAM_WIDE_WRITE #(
	parameter [63:0] INIT = 64'hx,
	parameter PORT_A_RD_WIDTH = 2,
	parameter PORT_A_WR_WIDTH = 8,
	parameter PORT_A_WR_EN_WIDTH = 2
) (
	input PORT_A_CLK,
	input PORT_A_RD_EN,
	input [5:0] PORT_A_ADDR,
	output reg [1:0] PORT_A_RD_DATA,
	input [1:0] PORT_A_WR_EN,
	input [7:0] PORT_A_WR_DATA
);

reg [63:0] mem;

initial mem = INIT;

always @(posedge PORT_A_CLK) begin
	if (PORT_A_RD_EN)
		PORT_A_RD_DATA <= mem[{PORT_A_ADDR[5:1],1'b0}+:2];
	if (PORT_A_WR_EN[0])
		mem[{PORT_A_ADDR[5:3],3'b000}+:4] <= PORT_A_WR_DATA[3:0];
	if (PORT_A_WR_EN[1])
		mem[{PORT_A_ADDR[5:3],3'b100}+:4] <= PORT_A_WR_DATA[7:4];
end

endmodule

