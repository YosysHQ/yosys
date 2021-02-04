`default_nettype none

module top1;
	generate
		if (1) begin : foo
			if (1) begin : bar
				wire x;
			end
			assign bar.x = 1;
			wire y;
		end
	endgenerate
endmodule

module top2;
	genvar i;
	generate
		if (1) begin : foo
			wire x;
			for (i = 0; i < 1; i = i + 1) begin : foo
				if (1) begin : foo
					assign x = 1;
				end
			end
		end
	endgenerate
endmodule
