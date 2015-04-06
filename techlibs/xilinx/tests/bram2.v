module myram(
	input		  rd_clk,
	input	   [ 7:0] rd_addr,
	output reg [15:0] rd_data,
	input		  wr_clk,
	input		  wr_enable,
	input	   [ 7:0] wr_addr,
	input	   [15:0] wr_data
);
	reg [15:0] memory [0:255];
	integer i;

	initial begin
		for (i = 0; i < 256; i = i+1)
			memory[i] = i;
	end

	always @(posedge rd_clk)
		rd_data <= memory[rd_addr];

	always @(posedge wr_clk)
		if (wr_enable)
			memory[wr_addr] <= wr_data;
endmodule
