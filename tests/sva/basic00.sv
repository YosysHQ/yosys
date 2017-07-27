module top (input clk, reset, antecedent, output reg consequent);
	always @(posedge clk)
		consequent <= reset ? 0 : antecedent;

`ifdef FAIL
	test_assert: assert property ( @(posedge clk) disable iff (reset) antecedent |-> consequent )
			else $error("Failed with consequent = ", $sampled(consequent));
`else
	test_assert: assert property ( @(posedge clk) disable iff (reset) antecedent |=> consequent )
			else $error("Failed with consequent = ", $sampled(consequent));
`endif
endmodule
