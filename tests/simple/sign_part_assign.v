module test (
	offset_i,
	data_o,
	data_ref_o
);
input wire  [ 2:0] offset_i;
output reg  [15:0] data_o;
output reg  [15:0] data_ref_o;

always @(*) begin
	// defaults
	data_o = '0;
	data_ref_o = '0;

	// partial assigns
	data_ref_o[offset_i+:4] = 4'b1111; // unsigned
	data_o[offset_i+:4] 	= 1'sb1;   // sign extension to 4'b1111
end

endmodule
