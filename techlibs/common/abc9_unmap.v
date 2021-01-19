(* techmap_celltype = "$__DFF_N__$abc9_flop $__DFF_P__$abc9_flop" *)
module $__DFF_x__$abc9_flop (input C, D, (* init = 1'b0 *) input Q, output n1);
  parameter _TECHMAP_CELLTYPE_ = "";
  generate if (_TECHMAP_CELLTYPE_ == "$__DFF_N__$abc9_flop")
    $_DFF_N_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ == "$__DFF_P__$abc9_flop")
    $_DFF_P_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  else if (_TECHMAP_CELLTYPE_ != "")
    $error("Unrecognised _TECHMAP_CELLTYPE_");
  endgenerate
endmodule

module $__ABC9_SCC_BREAKER (input [WIDTH-1:0] I, output [WIDTH-1:0] O);
parameter WIDTH = 0;
assign O = I;
endmodule
