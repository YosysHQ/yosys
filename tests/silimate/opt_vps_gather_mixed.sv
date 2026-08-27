// Multi-bit gathers where only some of them are foldable.
//
// Both banks read at the same affine index, but from different tables and with
// different lane counts: the 8-lane bank clears min_gather, the 2-lane bank does
// not. The unfoldable bank's $bmux cells must survive intact and keep driving
// their outputs.
//
// This is the shape that makes per-element-bit grouping unsafe. Keyed on a
// strided slice of the table rather than the whole table, one element bit of a
// cell could clear min_gather while another did not, and retiring the cell after
// folding the first would leave the second's bits undriven.
module opt_vps_gather_mixed (
	input  wire [15:0][3:0] tbl_a,
	input  wire [15:0][3:0] tbl_b,
	input  wire [3:0]       base,
	output reg  [7:0][3:0]  y_a,
	output reg  [1:0][3:0]  y_b
);
	always_comb begin
		for (int i = 0; i < 8; i++)
			y_a[i] = tbl_a[4'(base + 4'(i))];
		for (int j = 0; j < 2; j++)
			y_b[j] = tbl_b[4'(base + 4'(j))];
	end
endmodule
