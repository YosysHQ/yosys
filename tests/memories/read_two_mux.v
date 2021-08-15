// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk
// expect-rd-en \re
// expect-rd-srst-sig \reset
// expect-rd-srst-val 8'00000000

module top(input clk, input we, re, reset, input [7:0] addr, wdata, output reg [7:0] rdata);

reg [7:0] bram[0:255];
(* keep *) reg dummy;

always @(posedge clk) begin
	rdata <= re ? (reset ? 8'b0 : bram[addr]) : rdata;
	if (we)
		bram[addr] <= wdata;
end

endmodule
