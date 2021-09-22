`default_nettype none
module genblk_order_top(
	output wire out1,
	output wire out2
);
	generate
		if (1) begin : outer
			if (1) begin : foo
				wire x = 0;
				if (1) begin : foo
					wire x = 1;
					assign out1 = foo.x;
				end
				assign out2 = foo.x;
			end
		end
	endgenerate
endmodule
