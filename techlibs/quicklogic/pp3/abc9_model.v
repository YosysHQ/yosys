(* abc9_flop, lib_whitebox *)
module $__PP3_DFFEPC_SYNCONLY (
  output Q,
  input D,
  input CLK,
  input EN,
);

  dffepc ff (.Q(Q), .D(D), .CLK(CLK), .EN(EN), .PRE(1'b0), .CLR(1'b0));

endmodule
