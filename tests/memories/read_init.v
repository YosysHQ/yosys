// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk
// extra-memory-args -zeroinit

module top(input clk, input we, re, reset, input [7:0] addr, wdata, output reg [7:0] rdata);

reg [7:0] bram[0:255];
initial rdata = 0;

always @(posedge clk) begin
	rdata <= bram[addr];
	if (we)
		bram[addr] <= wdata;
end

endmodule
