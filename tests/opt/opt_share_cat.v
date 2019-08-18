module opt_share_test(
  input [15:0]  a,
  input [15:0]  b,
  input [15:0]  c,
  input [15:0]  d,
  input         sel,
  output [63:0] res,
  );

  reg [31: 0]   cat1 = {a+b, c+d};
  reg [31: 0]   cat2 = {a-b, c-d};

  assign res = {b, sel ? cat1 : cat2, a};

endmodule
