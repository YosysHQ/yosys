module top (
	input clk,
	input a, b
);
	default clocking @(posedge clk); endclocking

    wire a_copy;
    assign a_copy = a;

	assert property (
		$rose(a) |-> b
	);

`ifndef FAIL
	assume property (
		$rose(a_copy) |-> b
	);
`endif

endmodule
