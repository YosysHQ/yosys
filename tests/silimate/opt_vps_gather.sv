// Uniform per-bit gathers: every lane reads the same table at an index that is
// affine in the lane number, so the whole bank is one barrel shift.
//
// Two idioms from the address-decode designs this targets: an added dynamic
// amount, and a subtracted one. opt_expr renders the subtracted form as a
// narrow core with a constant-1 MSB extension, which the affine analysis has to
// read as a known addend for these lanes to land in one group.
module opt_vps_gather (
	input  wire [53:0] src,
	input  wire [2:0]  pbits,
	input  wire [2:0]  bank_lg2,
	input  wire [4:0]  pilv,
	output reg  [40:0] y_add,
	output reg  [40:0] y_sub
);
	integer p_i, b_i, pilv_i;
	always @* begin
		p_i    = pbits;
		b_i    = bank_lg2;
		pilv_i = pilv;
	end

	integer i;
	always @* begin
		for (i = 0; i <= 40; i = i + 1) begin
			if (i < pilv_i + 1)
				y_add[i] = src[i];
			else
				y_add[i] = src[6'(i + p_i + b_i)];
		end
	end

	integer j;
	always @* begin
		for (j = 0; j <= 40; j = j + 1) begin
			if (j < pilv_i + 1)
				y_sub[j] = src[j];
			else
				y_sub[j] = src[6'(j - p_i)];
		end
	end
endmodule
