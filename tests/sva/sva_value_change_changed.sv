module top (
	input clk,
	input a, b
);
	default clocking @(posedge clk); endclocking

	assert property (
		$changed(b)
	);

`ifndef FAIL
	assume property (
		b !== 'x ##1 $changed(b)
	);
`endif

endmodule
