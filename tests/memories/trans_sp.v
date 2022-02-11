// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk
// expect-rd-en \re

module top(input clk, we, re, input [7:0] addr, wd, output reg [7:0] rd);

reg [7:0] mem[0:255];

always @(posedge clk) begin
	if (we)
		mem[addr] <= wd;

	if (re) begin
		rd <= mem[addr];
		if (we)
			rd <= wd;
	end
end

endmodule
