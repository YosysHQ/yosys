// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk

module top(input clk, input we, re, reset, input [7:0] addr, wdata, output reg [7:0] rdata);

reg [7:0] bram[0:255];
(* keep *) reg dummy;

always @(posedge clk)
	if (reset)
		dummy <= 1'b0;
	else if (re)
		rdata <= bram[addr];
	else if (we)
		bram[addr] <= wdata;
endmodule
