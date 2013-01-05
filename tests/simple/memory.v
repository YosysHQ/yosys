
module test01(clk, wr_en, wr_addr, wr_value, rd_addr, rd_value);

input clk, wr_en;
input [3:0] wr_addr, rd_addr;
input [7:0] wr_value;
output reg [7:0] rd_value;

reg [7:0] data [15:0];

always @(posedge clk)
	if (wr_en)
		data[wr_addr] <= wr_value;

always @(posedge clk)
	rd_value <= data[rd_addr];

endmodule

