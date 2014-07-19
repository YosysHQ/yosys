// expect-wr-ports 1
// expect-rd-ports 1

module test(
	input clk,
	input wr_en1, wr_en2, wr_en3,
	input [3:0] wr_addr1, wr_addr2, wr_addr3,
	input [15:0] wr_data,
	input [3:0] rd_addr,
	output reg [31:0] rd_data
);

reg [31:0] mem [0:15];

always @(posedge clk) begin
	if (wr_en1)
		mem[wr_addr1][15:0] <= wr_data;
	else if (wr_en2)
		mem[wr_addr2][23:8] <= wr_data;
	else if (wr_en3)
		mem[wr_addr3][31:16] <= wr_data;
	rd_data <= mem[rd_addr];
end

endmodule
