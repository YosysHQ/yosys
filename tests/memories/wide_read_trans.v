// expect-wr-ports 1
// expect-rd-ports 4
// expect-rd-wide-continuation 4'1110

module test(
	input clk,
	input re,
	input we,
	input [5:0] ra,
	input [7:0] wa,
	input [7:0] wd,
	output reg [31:0] rd
);

reg [7:0] mem[0:255];

always @(posedge clk) begin
	if (re) begin
		rd[7:0] <= mem[{ra, 2'b00}];
		rd[15:8] <= mem[{ra, 2'b01}];
		rd[23:16] <= mem[{ra, 2'b10}];
		rd[31:24] <= mem[{ra, 2'b11}];
		if (we && wa == {ra, 2'b00})
			rd [7:0] <= wd;
		if (we && wa == {ra, 2'b01})
			rd [15:8] <= wd;
		if (we && wa == {ra, 2'b10})
			rd [23:16] <= wd;
		if (we && wa == {ra, 2'b11})
			rd [31:24] <= wd;
	end
end

always @(posedge clk) begin
	if (we)
		mem[wa] <= wd;
end

endmodule

