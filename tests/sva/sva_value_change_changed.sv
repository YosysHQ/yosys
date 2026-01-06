module top (
	input clk,
	input a, b
);
	default clocking @(posedge clk); endclocking

	assert property (
		$changed(b)
	);

	wire x = 'x;

`ifndef FAIL
	assume property (
		b !== x ##1 $changed(b)
	);
`endif

endmodule
