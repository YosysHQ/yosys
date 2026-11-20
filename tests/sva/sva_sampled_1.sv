module top (input clk, a, b, input [3:0] x);
	assume property (@(posedge clk) a |=> b);
`ifndef FAIL
	assert property (@(posedge clk) $sampled(x) == x);
	assert property (@(posedge clk) a |-> ##1 $sampled(b));
`else
	assert property (@(posedge clk) $sampled(x) != x);
`endif
endmodule

