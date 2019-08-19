module opt_share_test(
  input [15:0]  a,
  input [15:0]  b,
  input         sel,
  output [15:0] res,
  );

  assign res = {sel ? a + b : a - b};

endmodule
