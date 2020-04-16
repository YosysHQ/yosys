(* abc9_box *)
module \$__ABC9_DELAY (input I, output O);
  parameter DELAY = 0;
  specify
    (I => O) = DELAY;
  endspecify
endmodule

(* abc9_flop, abc9_box, lib_whitebox *)
module $__DFF_N__$abc9_flop(input C, D, Q, (* init=INIT *) output n1);
  parameter [0:0] INIT = 1'bx;
  assign n1 = D;
  specify
    $setup(D, posedge C, 0);
    (posedge C => (n1:D)) = 0;
  endspecify
endmodule

(* abc9_flop, abc9_box, lib_whitebox *)
module $__DFF_P__$abc9_flop(input C, D, Q, (* init=INIT *) output n1);
  parameter [0:0] INIT = 1'bx;
  assign n1 = D;
  specify
    $setup(D, posedge C, 0);
    (posedge C => (n1:D)) = 0;
  endspecify
endmodule
