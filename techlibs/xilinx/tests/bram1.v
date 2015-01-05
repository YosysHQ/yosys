module bram1 #(
	parameter ABITS = 8, DBITS = 8, TRANSP = 0
) (
	input clk,

	input [ABITS-1:0] WR_ADDR,
	input [DBITS-1:0] WR_DATA,
	input WR_EN,

	input [ABITS-1:0] RD_ADDR,
	output [DBITS-1:0] RD_DATA
);
	reg [DBITS-1:0] memory [0:2**ABITS-1];
	reg [ABITS-1:0] RD_ADDR_BUF;
	reg [DBITS-1:0] RD_DATA_BUF;

	always @(posedge clk) begin
		if (WR_EN) memory[WR_ADDR] <= WR_DATA;
		RD_ADDR_BUF <= RD_ADDR;
		RD_DATA_BUF <= memory[RD_ADDR];
	end

	assign RD_DATA = TRANSP ? memory[RD_ADDR_BUF] : RD_DATA_BUF;
endmodule
