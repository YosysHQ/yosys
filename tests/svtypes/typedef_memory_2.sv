module top(input [3:0] addr, wdata, input clk, wen, output reg [3:0] rdata);
	typedef logic [3:0] nibble;

	(nibble) mem[0:15];

	always @(posedge clk) begin
		if (wen) mem[addr] <= wdata;
		rdata <= mem[addr];
	end
endmodule
