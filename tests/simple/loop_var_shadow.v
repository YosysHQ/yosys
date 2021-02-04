module top(out);
	genvar i;
	generate
		for (i = 0; i < 2; i = i + 1) begin : loop
			localparam j = i + 1;
			if (1) begin : blk
				localparam i = j + 1;
				wire [i:0] x;
				assign x = 1'sb1;
			end
		end
	endgenerate
	output wire [63:0] out;
	assign out = {loop[0].blk.x, loop[1].blk.x};
endmodule
