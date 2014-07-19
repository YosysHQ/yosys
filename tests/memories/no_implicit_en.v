// expect-wr-ports 1
// expect-rd-ports 2

module test(clk, rd_addr, rd_data, cp_addr, wr_addr, wr_en, wr_data);

input clk;

input [3:0] rd_addr;
output reg [31:0] rd_data;

input [3:0] cp_addr, wr_addr, wr_en;
input [31:0] wr_data;

reg [31:0] mem [0:15];

always @(posedge clk) begin
	mem[wr_addr][ 7: 0] <= wr_en[0] ? wr_data[ 7: 0] : mem[cp_addr][ 7: 0];
	mem[wr_addr][15: 8] <= wr_en[1] ? wr_data[15: 8] : mem[cp_addr][15: 8];
	mem[wr_addr][23:16] <= wr_en[2] ? wr_data[23:16] : mem[cp_addr][23:16];
	mem[wr_addr][31:24] <= wr_en[3] ? wr_data[31:24] : mem[cp_addr][31:24];
	rd_data <= mem[rd_addr];
end

endmodule
