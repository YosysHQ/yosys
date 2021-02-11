module top(x);
	generate
		if (1) begin : blk
			wire x;
			assign x = 0;
		end
	endgenerate
	output wire x;
	assign x = blk.x;
endmodule
