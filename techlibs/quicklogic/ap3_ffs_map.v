module \$_DFFSRE_PPPP_ (input C, S, R, E, D, output Q);
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
  ff #(.INIT(1'b0)) _TECHMAP_REPLACE_ (.QCK(C), .QST(S), .QRT(R), .QEN(E), .D(D), .CQZ(Q));
endmodule
