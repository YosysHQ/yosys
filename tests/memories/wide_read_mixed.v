// expect-wr-ports 1
// expect-rd-ports 4
// expect-rd-wide-continuation 4'1110
// expect-rd-srst-val 32'10000111011001010100001100100001
// expect-rd-init-val 32'10101011110011011110111110101011

// In this testcase, the byte-wide read ports are merged into a single
// word-wide port despite mismatched transparency, with soft transparency
// logic inserted on half the port to preserve the semantics.

module test(
	input clk,
	input re, rr,
	input we,
	input [5:0] ra,
	input [7:0] wa,
	input [7:0] wd,
	output reg [31:0] rd
);

reg [7:0] mem[0:255];

initial rd = 32'habcdefab;

always @(posedge clk) begin
	if (rr) begin
		rd <= 32'h87654321;
	end else if (re) begin
		rd[7:0] <= mem[{ra, 2'b00}];
		rd[15:8] <= mem[{ra, 2'b01}];
		rd[23:16] <= mem[{ra, 2'b10}];
		rd[31:24] <= mem[{ra, 2'b11}];
		if (we && wa == {ra, 2'b00})
			rd [7:0] <= wd;
		if (we && wa == {ra, 2'b01})
			rd [15:8] <= wd;
	end
end

always @(posedge clk) begin
	if (we)
		mem[wa] <= wd;
end

endmodule

