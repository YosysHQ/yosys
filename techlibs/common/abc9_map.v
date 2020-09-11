`ifdef DFF
(* techmap_celltype = "$_DFF_[PN]_" *)
module $_DFF_x_(input C, D, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  parameter _TECHMAP_CELLTYPE_ = "";
  wire D_;
  generate if (_TECHMAP_CELLTYPE_ == "$_DFF_N_") begin
    if (_TECHMAP_WIREINIT_Q_ === 1'b0) begin
      $__DFF_N__$abc9_flop _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q), .n1(D_));
      $_DFF_N_ ff (.C(C), .D(D_), .Q(Q));
    end
    else
      (* abc9_keep *) $_DFF_N_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  end
  else if (_TECHMAP_CELLTYPE_ == "$_DFF_P_") begin
    if (_TECHMAP_WIREINIT_Q_ === 1'b0) begin
      $__DFF_P__$abc9_flop _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q), .n1(D_));
      $_DFF_P_ ff (.C(C), .D(D_), .Q(Q));
    end
    else
      (* abc9_keep *) $_DFF_P_ _TECHMAP_REPLACE_ (.C(C), .D(D), .Q(Q));
  end
  else if (_TECHMAP_CELLTYPE_ != "")
    $error("Unrecognised _TECHMAP_CELLTYPE_");
  endgenerate
endmodule
`endif
