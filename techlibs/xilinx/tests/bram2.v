module myram(
	input		  rd_clk,
	input	   [ 7:0] rd_addr,
	output reg [17:0] rd_data,
	input		  wr_clk,
	input		  wr_enable,
	input	   [ 7:0] wr_addr,
	input	   [17:0] wr_data
);
	reg [17:0] memory [0:255];
	integer i;

	function [17:0] hash(input [7:0] k);
		reg [31:0] x;
		begin
			x = {k, ~k, k, ~k};
			x = x ^ (x << 13);
			x = x ^ (x >> 17);
			x = x ^ (x << 5);
			hash = x;
		end
	endfunction

	initial begin
		for (i = 0; i < 256; i = i+1)
			memory[i] = hash(i);
	end

	always @(posedge rd_clk)
		rd_data <= memory[rd_addr];

	always @(posedge wr_clk)
		if (wr_enable)
			memory[wr_addr] <= wr_data;
endmodule
