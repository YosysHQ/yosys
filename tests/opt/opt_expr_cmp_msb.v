module top(
  a, b, x,
  o1_1, o1_2, o1_3, o1_4,
  o2_1, o2_2, o2_3, o2_4,
  o3_1, o3_2, o3_3, o3_4,
  o4_1, o4_2, o4_3, o4_4,
  o5_1, o5_2, o5_3, o5_4
);
  input [3:0] a;
  input b;
  input [7:0] x;

  output o1_1, o1_2, o1_3, o1_4;
  output o2_1, o2_2, o2_3, o2_4;
  output o3_1, o3_2, o3_3, o3_4;
  output o4_1, o4_2, o4_3, o4_4;
  output o5_1, o5_2, o5_3, o5_4;

  // RHS = {b, 4'b0000}: same width as `a`, lower bits zero.
  assign o1_1 = a <  {b, 4'b0000};
  assign o1_2 = a >= {b, 4'b0000};
  assign o1_3 = {b, 4'b0000} >  a;
  assign o1_4 = {b, 4'b0000} <= a;

  // RHS = {b, 5'b00000}: wider than `a`; `a` zero-extends to fit.
  assign o2_1 = a <  {b, 5'b00000};
  assign o2_2 = a >= {b, 5'b00000};
  assign o2_3 = {b, 5'b00000} >  a;
  assign o2_4 = {b, 5'b00000} <= a;

  // LHS = {1'b0, a}: explicit zero-extend on the bounded operand.
  assign o3_1 = {1'b0, a} <  {b, 4'b0000};
  assign o3_2 = {1'b0, a} >= {b, 4'b0000};
  assign o3_3 = {b, 4'b0000} >  {1'b0, a};
  assign o3_4 = {b, 4'b0000} <= {1'b0, a};

  // Lowered form of `(signed x < -1)` after sign-stripping:
  //   A = {1'b1, x[N-2:0]}, B = {x[N-1], (N-1)'b1}, both unsigned.
  // Expected: Y = x[N-1] && ~&x[N-2:0]
  assign o4_1 = {1'b1, x[6:0]} <  {x[7], 7'b1111111};
  assign o4_2 = {1'b1, x[6:0]} >= {x[7], 7'b1111111};
  assign o4_3 = {x[7], 7'b1111111} >  {1'b1, x[6:0]};
  assign o4_4 = {x[7], 7'b1111111} <= {1'b1, x[6:0]};

  // Same pattern at width = 2 (smallest viable N).
  assign o5_1 = {1'b1, x[0]} <  {x[1], 1'b1};
  assign o5_2 = {1'b1, x[0]} >= {x[1], 1'b1};
  assign o5_3 = {x[1], 1'b1} >  {1'b1, x[0]};
  assign o5_4 = {x[1], 1'b1} <= {1'b1, x[0]};
endmodule
