// ---------------------------------------

(* abc9_box *)
module \$__ABC9_DPR16X4_COMB (input [3:0] $DO, RAD, output [3:0] DO);
  specify
    ($DO => DO) = 0;
    (RAD[0] *> DO) = 141;
    (RAD[1] *> DO) = 379;
    (RAD[2] *> DO) = 275;
    (RAD[3] *> DO) = 379;
  endspecify
endmodule
