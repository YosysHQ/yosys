// Uniform zero-fill gather whose index can go negative: `idx - 1 + a + b` is
// below zero for the bottom lane when a and b are both zero.
//
// Verific spells a narrow sum that may go negative by inverting the MSB of an
// unsigned sum -- {~c, s} read as signed equals {c, s} - 2^(w-1). Only the
// bottom lane needs that form, so without -msb-inv-sext its index reduces to a
// different set of affine atoms than the lanes above it and it lands in a group
// of its own, surviving as a second barrel beside the folded one.
module opt_vps_gather_negidx (
	input  wire [53:0] hi_addr,
	input  wire [53:0] lo_addr,
	input  wire [2:0]  mid_w,
	input  wire [2:0]  bank_lg2,
	input  wire [3:0]  lo_w,
	output reg  [53:0] pre_blk
);
	integer bank_n, lo_w_n;
	always @(*) begin
		bank_n = bank_lg2;
		lo_w_n = lo_w;
	end

	// Read at bit 0 of an explicit variable shift, which is the zero-fill gather
	// shape Y[k] = A[B + k]; a plain bit-select would take the modular path.
	reg [52:0] blk_shft;
	integer idx;
	always @(*) begin
		blk_shft = 53'd0;
		for (idx = 0; idx <= 53; idx = idx + 1) begin
			if (idx < lo_w_n + 1)
				pre_blk[idx] = lo_addr[idx];
			else begin
				blk_shft = hi_addr[53:1] >> (idx - 1 + mid_w + bank_n);
				pre_blk[idx] = blk_shft[0];
			end
		end
	end
endmodule
