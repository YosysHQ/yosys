// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk
// expect-rd-en \re

module top(input clk, we, re, input [7:0] ra, wa, wd, output reg [7:0] rd);

reg [7:0] mem[0:255];

always @(posedge clk) begin
	if (we)
		mem[wa] <= wd;

	if (re) begin
		rd <= mem[ra];
		if (we && ra == wa)
			rd <= wd;
	end
end

endmodule
