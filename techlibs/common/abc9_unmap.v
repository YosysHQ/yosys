(* techmap_celltype = "$__DFF_N__$abc9_flop $__DFF_P__$abc9_flop" *)
module $__DFF_x__$abc9_flop (input C, D, Q, (* init = INIT *) output n1);
  parameter [0:0] INIT = 1'bx;
  parameter _TECHMAP_CELLTYPE_ = "";
  generate if (_TECHMAP_CELLTYPE_ == "$__DFF_N__$abc9_flop")
    $_DFF_N_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ == "$__DFF_P__$abc9_flop")
    $_DFF_P_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ != "")
    $error("Unrecognised _TECHMAP_CELLTYPE_");
  endgenerate
endmodule

(* techmap_celltype = "$__DFF_N_ $__DFF_P_" *)
module $__DFF_N__$abc9_flop(input C, D, output Q);
  parameter _TECHMAP_CELLTYPE_ = "";
  generate if (_TECHMAP_CELLTYPE_ == "$__DFF_N_")
    $_DFF_N_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ == "$__DFF_P_")
    $_DFF_P_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ != "")
    $error("Unrecognised _TECHMAP_CELLTYPE_");
  endgenerate
endmodule
