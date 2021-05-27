// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk
// expect-rd-en \re
// expect-rd-arst-sig \reset
// expect-rd-arst-val 8'01011010
// expect-rd-init-val 8'00111100

module top(input clk, input we, re, reset, input [7:0] addr, wdata, output reg [7:0] rdata);

reg [7:0] bram[0:255];
initial rdata = 8'h3c;

always @(posedge clk) begin
	if (we)
		bram[addr] <= wdata;
end

always @(posedge clk, posedge reset) begin
	if (reset)
		rdata <= 8'h5a;
	else if (re)
		rdata <= bram[addr];
end

endmodule

