module bram #(
	parameter ABITS = 8, DBITS = 8,
	parameter INIT_ADDR = 0, INIT_DATA = 0
) (
	input clk,

	input [ABITS-1:0] WR_ADDR,
	input [DBITS-1:0] WR_DATA,
	input WR_EN,

	input [ABITS-1:0] RD_ADDR,
	output reg [DBITS-1:0] RD_DATA
);
	reg [DBITS-1:0] memory [0:2**ABITS-1];

	initial begin
		memory[INIT_ADDR] <= INIT_DATA;
	end

	always @(posedge clk) begin
		if (WR_EN) memory[WR_ADDR] <= WR_DATA;
		RD_DATA <= memory[RD_ADDR];
	end
endmodule
