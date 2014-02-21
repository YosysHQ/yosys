module MEM4X1 (CLK, RD_ADDR, RD_DATA, WR_ADDR, WR_DATA, WR_EN);
	input CLK, WR_DATA, WR_EN;
	input [3:0] RD_ADDR, WR_ADDR;
	output reg RD_DATA;

	reg [15:0] memory;

	always @(posedge CLK) begin
		if (WR_EN)
			memory[WR_ADDR] <= WR_DATA;
		RD_DATA <= memory[RD_ADDR];
	end
endmodule
