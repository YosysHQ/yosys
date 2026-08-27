// Multi-bit gathers over tables that OVERLAP but are not identical.
//
// This is the only shape that tells the two candidate grouping keys apart. Test
// 17's banks read wholly disjoint tables, so no strided slice of one bank's
// table ever equals a slice of the other's and every cell folds all-or-nothing
// either way.
//
// Here element bit 0 of every entry is `shared[e]` in all four overlap lanes,
// while element bit 1 is private to the lane. Keyed on the whole A port the four
// lanes are four distinct tables, so they are four groups of one and none of
// them folds. Keyed on a stride-WIDTH slice of A instead, the four bit-0 slices
// are one identical SigSpec and clear min_gather while each bit-1 slice is a
// group of one that does not -- folding bit 0 then retires all four cells and
// leaves y_ovl[l][1] with no driver at all.
//
// The second bank reads a wholly shared table and must still fold, so the
// overlap bank surviving cannot be explained by the fold simply never firing.
module opt_vps_gather_overlap (
	input  wire [3:0]      shared, // element bit 0, common to all overlap lanes
	input  wire [3:0][3:0] priv,   // element bit 1, private to each overlap lane
	input  wire [3:0][1:0] utbl,   // wholly shared table for the foldable bank
	input  wire [1:0]      idx,
	output wire [3:0][1:0] y_ovl,
	output wire [3:0][1:0] y_uni
);
	wire [3:0][3:0][1:0] tbl;

	genvar l, e;
	generate
		// Per-lane tables agree on element bit 0 and differ on element bit 1.
		for (l = 0; l < 4; l = l + 1) begin : lanes
			for (e = 0; e < 4; e = e + 1) begin : entries
				assign tbl[l][e] = {priv[l][e], shared[e]};
			end
			assign y_ovl[l] = tbl[l][2'(idx + 2'(l))];
			assign y_uni[l] = utbl[2'(idx + 2'(l))];
		end
	endgenerate
endmodule
