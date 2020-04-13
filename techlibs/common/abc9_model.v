(* abc9_box *)
module \$__ABC9_DELAY (input I, output O);
  parameter DELAY = 0;
  specify
    (I => O) = DELAY;
  endspecify
endmodule
