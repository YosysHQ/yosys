module RAM_WIDE_READ #(
	parameter [63:0] INIT = 64'hx,
	parameter PORT_A_RD_WIDTH = 8,
	parameter PORT_A_WR_WIDTH = 2
) (
	input PORT_A_CLK,
	input PORT_A_RD_EN,
	input [5:0] PORT_A_ADDR,
	output reg [7:0] PORT_A_RD_DATA,
	input PORT_A_WR_EN,
	input [1:0] PORT_A_WR_DATA
);

reg [63:0] mem;

initial mem = INIT;

always @(posedge PORT_A_CLK) begin
	if (PORT_A_RD_EN)
		PORT_A_RD_DATA <= mem[{PORT_A_ADDR[5:3], 3'b000}+:8];
	if (PORT_A_WR_EN)
		mem[{PORT_A_ADDR[5:1],1'b0}+:2] <= PORT_A_WR_DATA;
end

endmodule
