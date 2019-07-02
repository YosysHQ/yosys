// expect-wr-ports 1
// expect-rd-ports 1
// expect-no-rd-clk

module top(input clk, input we, re, reset, input [7:0] addr, wdata, output reg [7:0] rdata);

reg [7:0] bram[0:255];
(* keep *) reg dummy;

always @(posedge clk) begin
	rdata <= re ? (reset ? 8'b0 : bram[addr]) : rdata;
	if (we)
		bram[addr] <= wdata;
end

endmodule
