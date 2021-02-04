module top #(
	parameter WIDTH = 6
) (
	input [WIDTH-1:0] a_i,
	input [WIDTH-1:0] b_i,
	output [WIDTH-1:0] z_o
);
	genvar g;
	generate
		for (g = 0; g < WIDTH; g = g + 1) begin
			if (g > 2) begin
				wire tmp;
				assign tmp = a_i[g] || b_i[g];
				assign z_o[g] = tmp;
			end
			else begin
				assign z_o[g] = a_i[g] && b_i[g];
			end
		end
	endgenerate
endmodule
