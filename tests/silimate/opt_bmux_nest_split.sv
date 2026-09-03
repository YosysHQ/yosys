// Rows-of-words memory read at a variable base with a fixed per-lane stride, with the
// flat element pointer split into a row field and a column field. This is the shape the
// pass exists for: Verific lowers `mem[p[hi]][p[lo]]` per lane as one row select per
// column plus one column select, so each lane ends up reading a table of its own.
//
// That private table is what blocks opt_vps: its uniform-gather folding groups
// candidates by their table, so every lane is a singleton group and a sliding window
// that should be one barrel shift per element bit folds not at all. Flatten the nest
// first and all LANES lanes share one table.
module opt_bmux_nest_split #(
    parameter int ROWS  = 4,
    parameter int COLS  = 8,
    parameter int EW    = 4,
    parameter int LANES = 6
  ) (
    input  logic [ROWS-1:0][COLS-1:0][EW-1:0] mem,
    input  logic [$clog2(ROWS*COLS)-1:0]      base,
    output logic [LANES-1:0][EW-1:0]          y
  );

  localparam int RW = $clog2(ROWS);
  localparam int CW = $clog2(COLS);

  logic [RW+CW-1:0] p;  // module-level scratch, as in the design this models

  always_comb
    for (int i = 0; i < LANES; i++) begin
      p = (RW+CW)'(base + (RW+CW)'(i));
      y[i] = mem[p[CW+:RW]][p[CW-1:0]];
    end

endmodule
