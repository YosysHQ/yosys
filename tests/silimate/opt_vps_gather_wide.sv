// opt_vps_gather.sv, but gathering elements wider than one bit.
//
// Every lane reads a 4-bit entry at an index affine in the lane number, so
// Verific emits one WIDTH=4 $bmux per lane rather than the 1-bit $bmux the fold
// used to be limited to. Each bank is still a single sliding window, and folds
// to one barrel shift per element bit: W barrels over M entries cost what one
// barrel over W*M bits would, so splitting the fold per bit is free.
//
// Two banks, added and subtracted index, as in the byte-FIFO staging windows
// this targets. They cannot share a group, so each cell contributes a candidate
// to W groups and is retired by whichever of them folds first.
module opt_vps_gather_wide (
	input  wire [15:0][3:0] tbl,
	input  wire [3:0]       base,
	input  wire [3:0]       skew,
	output reg  [7:0][3:0]  y_add,
	output reg  [7:0][3:0]  y_sub
);
	always @* begin
		for (int i = 0; i < 8; i++)
			y_add[i] = tbl[4'(base + 4'(i))];
		for (int j = 0; j < 8; j++)
			y_sub[j] = tbl[4'(skew - 4'(j))];
	end
endmodule
