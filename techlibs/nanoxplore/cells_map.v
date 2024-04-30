`default_nettype none

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      localparam [15:0] INIT = {{2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}},
                                {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(1'b0), .I3(1'b0), .I4(1'b0));
    end else
    if (WIDTH == 2) begin
      localparam [15:0] INIT = {{4{LUT[3:0]}}, {4{LUT[3:0]}}, {4{LUT[3:0]}}, {4{LUT[3:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(1'b0), .I4(1'b0), );
    end else
    if (WIDTH == 3) begin
      localparam [15:0] INIT = {{8{LUT[7:0]}}, {8{LUT[7:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(A[2]), .I4(1'b0));
    end else
    if (WIDTH == 4) begin
      NX_LUT #(.lut_table(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(A[2]), .I4(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule

(* techmap_celltype = "$_DFF_[NP]P[01]_" *)
module \$_DFF_xxxx_ (input D, C, R, output Q);
	parameter _TECHMAP_CELLTYPE_ = "";
  localparam dff_edge = _TECHMAP_CELLTYPE_[3*8 +: 8] == "N";
  localparam dff_type = _TECHMAP_CELLTYPE_[1*8 +: 8] == "1";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(dff_type), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b0), .dff_type(dff_type)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b1), .R(R), .O(Q));
endmodule

(* techmap_celltype = "$_SDFF_[NP]P[01]_" *)
module \$_SDFF_xxxx_ (input D, C, R, output Q);
	parameter _TECHMAP_CELLTYPE_ = "";
  localparam dff_edge = _TECHMAP_CELLTYPE_[3*8 +: 8] == "N";
  localparam dff_type = _TECHMAP_CELLTYPE_[1*8 +: 8] == "1";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(dff_type), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b1), .dff_type(dff_type)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b1), .R(R), .O(Q));
endmodule

(* techmap_celltype = "$_DFFE_[NP]P[01]P_" *)
module \$_DFFE_xxxx_ (input D, C, R, E, output Q);
	parameter _TECHMAP_CELLTYPE_ = "";
  localparam dff_edge = _TECHMAP_CELLTYPE_[4*8 +: 8] == "N";
  localparam dff_type = _TECHMAP_CELLTYPE_[2*8 +: 8] == "1";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(dff_type), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b1), .dff_sync(1'b0), .dff_type(dff_type)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(E), .R(R), .O(Q));
endmodule

(* techmap_celltype = "$_SDFFE_[NP]P[01]P_" *)
module \$_SDFFE_xxxx_ (input D, C, R, E, output Q);
	parameter _TECHMAP_CELLTYPE_ = "";
  localparam dff_edge = _TECHMAP_CELLTYPE_[4*8 +: 8] == "N";
  localparam dff_type = _TECHMAP_CELLTYPE_[2*8 +: 8] == "1";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(dff_type), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b1), .dff_sync(1'b1), .dff_type(dff_type)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(E), .R(R), .O(Q));
endmodule

module \$_DFF_P_ (input D, C, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(_TECHMAP_WIREINIT_Q_), .dff_edge(1'b0), .dff_init(1'b0), .dff_load(1'b0), .dff_sync(1'b0), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b1), .R(1'b0), .O(Q));
endmodule

module \$_DFF_N_ (input D, C, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(_TECHMAP_WIREINIT_Q_), .dff_edge(1'b1), .dff_init(1'b0), .dff_load(1'b0), .dff_sync(1'b0), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b1), .R(1'b0), .O(Q));
endmodule

module \$_DFFE_PP_ (input D, C, E, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(_TECHMAP_WIREINIT_Q_), .dff_edge(1'b0), .dff_init(1'b0), .dff_load(1'b1), .dff_sync(1'b0), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(E), .R(1'b0), .O(Q));
endmodule

module \$_DFFE_NP_ (input D, C, E, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(_TECHMAP_WIREINIT_Q_), .dff_edge(1'b1), .dff_init(1'b0), .dff_load(1'b1), .dff_sync(1'b0), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(E), .R(1'b0), .O(Q));
endmodule
