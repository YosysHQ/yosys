module top (
	input clk,
	input a, b, c, d
);
	default clocking @(posedge clk); endclocking

	assert property (
		a |=> b throughout (c ##1 d)
	);

`ifndef FAIL
	assume property (
		a |=> b && c
	);
	assume property (
		b && c |=> b && d
	);
`endif
endmodule
