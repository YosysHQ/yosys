module top(
	input wire x,
	output reg y
);
	localparam I = 1;
	genvar i;
	generate
		for (i = 0; i < 1; i = i + 1) begin : blk
			wire [i:i] z = x;
		end
	endgenerate
	always @* begin
		case (blk[I - 1].z)
			1: y = 0;
			0: y = 1;
		endcase
	end
endmodule
