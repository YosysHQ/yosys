// Three-level index split, to exercise convergence: the middle selects are themselves
// outer cells of a nest, so the outermost one cannot fold in the same round and has to
// wait for the round after.
module opt_bmux_nest_deep (
    input  logic [3:0][3:0][3:0][3:0] mem,
    input  logic [5:0]                p,
    output logic [3:0]                y
  );

  assign y = mem[p[5:4]][p[3:2]][p[1:0]];

endmodule
