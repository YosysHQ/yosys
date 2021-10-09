// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk

module top(input clk, we, rae, input [7:0] addr, wd, output [7:0] rd);

reg [7:0] mem[0:255];

reg [7:0] rra;

always @(posedge clk) begin
	if (we)
		mem[addr] <= wd;

	if (rae)
		rra <= addr;
end

assign rd = mem[rra];

endmodule
