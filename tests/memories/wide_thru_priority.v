// expect-wr-ports 3
// expect-rd-ports 1
// expect-wr-wide-continuation 3'010

module test(
	input clk,
	input we1, we2,
	input [5:0] ra,
	input [4:0] wa1,
	input [5:0] wa2,
	input [15:0] wd1,
	input [7:0] wd2,
	output [7:0] rd
);

reg [7:0] mem[0:63];

assign rd = mem[ra];

always @(posedge clk) begin
	if (we1)
		mem[{wa1, 1'b0}] <= wd1[7:0];
	if (we2)
		mem[wa2] <= wd2;
	if (we1)
		mem[{wa1, 1'b1}] <= wd1[15:8];
end

endmodule
