// expect-wr-ports 2
// expect-rd-ports 1
// expect-wr-wide-continuation 2'10

module test(
	input clk,
	input [3:0] we,
	input [6:0] ra,
	input [5:0] wa,
	input [31:0] wd,
	output [15:0] rd
);

reg [7:0] mem[3:254];

assign rd[7:0] = mem[{ra, 1'b0}];
assign rd[15:0] = mem[{ra, 1'b1}];

initial begin
	mem[5] = 8'h12;
	mem[6] = 8'h34;
	mem[7] = 8'h56;
end

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
