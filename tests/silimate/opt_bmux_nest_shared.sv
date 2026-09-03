// Two column selects over one row-selected table: both reads share the row index, so
// Verific emits the row selects once and both column selects read them.
//
// Flattening either outer would leave those row selects alive for the other, so the
// design would pay their mux trees plus a wider flat select. The pass declines, which
// is what test 3 pins.
module opt_bmux_nest_shared (
    input  logic [3:0][7:0][3:0] mem,
    input  logic [1:0]           r,
    input  logic [2:0]           c0,
    input  logic [2:0]           c1,
    output logic [3:0]           y0,
    output logic [3:0]           y1
  );

  assign y0 = mem[r][c0];
  assign y1 = mem[r][c1];

endmodule
