// Uniform zero-fill gathers indexed by `base + lane`, where `base` is a
// declared wire holding a sum of two operands of its own width.
//
// That sum truncates, so its affine interval is [0, 2*2^w - 2] against a
// modulus of 2^w: the form describes the wire only modulo 2^w and no offset
// makes it exact. Every `base + lane` built on it then loses exactness, falls
// back to an opaque per-lane atom, and each lane lands in a gather group of
// its own -- so a farm of one barrel per lane survives instead of the single
// shared barrel. -wrap-atom reads such a wire as its own bounded atom.
//
// The `fit` bank is the near-miss: the same shape, but its operands are narrow
// enough that the sum provably stays inside the modulus, so the sum form is
// already exact and the bank folds with or without the flag.
module opt_vps_gather_wrapbase (
	input  wire [53:0] wrap_addr,
	input  wire [53:0] fit_addr,
	input  wire [53:0] lo_addr,
	input  wire [5:0]  part_w,
	input  wire [5:0]  bank_w,
	input  wire [2:0]  small_a,
	input  wire [2:0]  small_b,
	input  wire [3:0]  lo_w,
	output reg  [53:0] wrap_blk,
	output reg  [53:0] fit_blk
);
	// Sum at the width of its own operands: wraps, so the interval is useless
	wire [5:0] wrap_base = part_w + bank_w;

	// Same spelling, but 3-bit operands cannot carry out of 6 bits
	wire [5:0] fit_base = {3'b000, small_a} + {3'b000, small_b};

	integer lo_w_n;
	always @(*) lo_w_n = lo_w;

	// Read at bit 0 of an explicit variable shift, which is the zero-fill gather
	// shape Y[k] = A[B + k]; a plain bit-select would take the modular path.
	reg [52:0] wrap_shft;
	integer i;
	always @(*) begin
		wrap_shft = 53'd0;
		for (i = 0; i <= 53; i = i + 1) begin
			if (i < lo_w_n + 1)
				wrap_blk[i] = lo_addr[i];
			else begin
				wrap_shft = wrap_addr[53:1] >> (wrap_base + i - 1);
				wrap_blk[i] = wrap_shft[0];
			end
		end
	end

	reg [52:0] fit_shft;
	integer j;
	always @(*) begin
		fit_shft = 53'd0;
		for (j = 0; j <= 53; j = j + 1) begin
			if (j < lo_w_n + 1)
				fit_blk[j] = lo_addr[j];
			else begin
				fit_shft = fit_addr[53:1] >> (fit_base + j - 1);
				fit_blk[j] = fit_shft[0];
			end
		end
	end
endmodule
