module \$_DLATCH_P_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = E ? D : Q;
endmodule

module \$_DLATCH_N_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = !E ? D : Q;
endmodule
