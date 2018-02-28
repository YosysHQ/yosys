module top (
	input clk,
	input a, b, c, d
);
	default clocking @(posedge clk); endclocking

	assert property (
		a ##[*] b |=> c until d
	);

`ifndef FAIL
	assume property (
		b |=> ##5 d
	);
	assume property (
		b || (c && !d) |=> c
	);
`endif
endmodule
