// Circular-index gathers guarded with `% N`, where only one of the guards can
// actually wrap.
//
// `win` reads the table at `i + off`, which peaks at 21 + 31 = 52 and so never
// reaches the 54 the modulo divides by: the guard is dead and the loop is a
// plain window read that folds into one barrel over `blk`. `rot` reads its own
// 22-entry source at `i + rt`, which runs to 52 and does wrap, so that loop is
// a rotate and has to stay per-bit selects.
//
// `blk` ahead of the first loop makes the folded gather read a slice of another
// barrel's output, so the fold has to leave a shape the shift passes can merge.
module opt_vps_gather_deadmod (
	input  wire [53:0] tbl,
	input  wire [4:0]  sh,
	input  wire [4:0]  off,
	input  wire [4:0]  rt,
	output reg  [21:0] win,
	output reg  [21:0] rot
);
	wire [53:0] blk = tbl >> sh;

	integer i;
	always @(*)
		for (i = 0; i < 22; i = i + 1)
			win[i] = blk[(i + off) % 54];

	integer j;
	always @(*)
		for (j = 0; j < 22; j = j + 1)
			rot[j] = win[(j + rt) % 22];
endmodule
