/*(* abc9_box, lib_whitebox *)
module \$__AP3_CARRY_WRAPPER (
  (* abc9_carry *)
  output CO,
  output O,
  input A,
  B,
  (* abc9_carry *)
  input CI,
  input I2,
  I3
);
  parameter LUT = 0;
  parameter I2_IS_CI = 0;
  wire I2_OR_CI = I2_IS_CI ? CI : I2;
  QL_CARRY carry (
    .I0(A),
    .I1(B),
    .CI(CI),
    .CO(CO)
  );
  LUT4 #(
    .INIT(LUT)
  ) adder (
    .I0(A),
    .I1(B),
    .I2(I2_OR_CI),
    .I3(I3),
    .O(O)
  );
endmodule */

(* abc9_flop, lib_whitebox *)
module \$__PP3_DFFEPC_SYNCONLY (
  output reg Q,
  input D,
  input CLK,
  input EN,
);

  dffepc ff (.Q(Q), .D(D), .CLK(CLK), .EN(EN), .PRE(1'b0), .CLR(1'b0));

endmodule
