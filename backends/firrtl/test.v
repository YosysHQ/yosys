module test(
	input clk, wen,
	input [4:0] waddr, raddr,
	input [31:0] wdata,
	output reg [31:0] rdata,
	signed input [7:0] a, b, x,
	output [15:0] s, d, y, z, u, q
);
	reg [31:0] memory [0:31];

	always @(posedge clk) begin
		rdata <= memory[raddr];
		if (wen) memory[waddr] <= wdata;
	end

	assign s = a+{b[6:2], 2'b1};
	assign d = a-b;
	assign y = x;
	assign z[7:0] = s+d;
	assign z[15:8] = s-d;

	always @(posedge clk)
		q <= s ^ d ^ x;
endmodule
