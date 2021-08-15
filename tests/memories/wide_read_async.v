// expect-wr-ports 1
// expect-rd-ports 4
// expect-rd-wide-continuation 4'1110

module test(
	input clk,
	input we,
	input [5:0] ra,
	input [7:0] wa,
	input [7:0] wd,
	output [31:0] rd
);

reg [7:0] mem[0:255];

assign rd[7:0] = mem[{ra, 2'b00}];
assign rd[15:8] = mem[{ra, 2'b01}];
assign rd[23:16] = mem[{ra, 2'b10}];
assign rd[31:24] = mem[{ra, 2'b11}];

always @(posedge clk) begin
	if (we)
		mem[wa] <= wd;
end

endmodule

