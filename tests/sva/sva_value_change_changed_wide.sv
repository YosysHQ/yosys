module top (
	input clk,
	input [2:0] a,
	input [2:0] b
);
	default clocking @(posedge clk); endclocking

	assert property (
		$changed(a)
	);

    assert property (
        $changed(b) == ($changed(b[0]) || $changed(b[1]) || $changed(b[2]))
    );

`ifndef FAIL
	assume property (
		a !== 'x ##1 $changed(a)
	);
`endif

endmodule
