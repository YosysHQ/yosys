// expect-wr-ports 4
// expect-rd-ports 1
// expect-wr-wide-continuation 4'1110

module test(
	input clk,
	input [3:0] we,
	input [7:0] ra,
	input [5:0] wa,
	input [31:0] wd,
	output [7:0] rd
);

reg [7:0] mem[0:255];

assign rd = mem[ra];

always @(posedge clk) begin
	if (we[0])
		mem[{wa, 2'b00}] <= wd[7:0];
	if (we[1])
		mem[{wa, 2'b01}] <= wd[15:8];
	if (we[2])
		mem[{wa, 2'b10}] <= wd[23:16];
	if (we[3])
		mem[{wa, 2'b11}] <= wd[31:24];
end

endmodule
