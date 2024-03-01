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
module dff(input D, C, R, output Q);
	parameter _TECHMAP_CELLTYPE = "$_DFF_PP1_";
  localparam dff_edge = _TECHMAP_CELLTYPE[6*8 +: 8] == "N";
  localparam dff_type = _TECHMAP_CELLTYPE[8*8 +: 8] == "1";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b0), .dff_type(dff_type)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b0), .R(R), .O(Q));
endmodule

(* techmap_celltype = "$_ALDFF_[NP]P_" *)
module aldff(input D, C, L, AD, output Q);
	parameter _TECHMAP_CELLTYPE = "$_ALDFF_PP_";
  localparam dff_edge = _TECHMAP_CELLTYPE[8*8 +: 8] == "N";
  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(dff_edge), .dff_init(1'b1), .dff_load(1'b1), .dff_sync(1'b0), .dff_type(2)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(AD), .R(L), .O(Q));
endmodule

module \$_SDFF_PP0_ (input D, C, R, output Q);
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(1'b0), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b1), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b0), .R(R), .O(Q));
endmodule

module \$_SDFF_PP1_ (input D, C, R, output Q);
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(1'b0), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b1), .dff_type(1'b1)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b0), .R(R), .O(Q));
endmodule

module \$_SDFF_NP0_ (input D, C, R, output Q);
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(1'b1), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b1), .dff_type(1'b0)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b0), .R(R), .O(Q));
endmodule

module \$_SDFF_NP1_ (input D, C, R, output Q);
  NX_DFF #(.dff_ctxt(1'b0), .dff_edge(1'b1), .dff_init(1'b1), .dff_load(1'b0), .dff_sync(1'b1), .dff_type(1'b1)) _TECHMAP_REPLACE_ (.I(D), .CK(C), .L(1'b0), .R(R), .O(Q));
endmodule

module $__NX_XRFB_64x18_ (input PORT_W_CLK, input [5:0] PORT_W_ADDR, PORT_R_ADDR, input [17:0] PORT_W_WR_DATA, input PORT_W_WR_EN, output [17:0] PORT_R_RD_DATA);
  parameter INIT = 1152'bx;
  parameter PORT_W_CLK_POL = 1'b1;
  NX_XRFB_64x18 #(.mem_ctxt(INIT), .wck_edge(~PORT_W_CLK_POL)) _TECHMAP_REPLACE_ (.WCK(PORT_W_CLK), .I(PORT_W_WR_DATA), .RA(PORT_R_ADDR), .WA(PORT_W_ADDR), .WE(PORT_W_WR_EN), .WEA(1'b1), .O(PORT_R_RD_DATA));
endmodule

module $__NX_XRFB_32x36_ (input PORT_W_CLK, input [4:0] PORT_W_ADDR, PORT_R_ADDR, input [35:0] PORT_W_WR_DATA, input PORT_W_WR_EN, output [35:0] PORT_R_RD_DATA);
  parameter INIT = 1152'bx;
  parameter PORT_W_CLK_POL = 1'b1;
  NX_XRFB_32x36 #(.mem_ctxt(INIT), .wck_edge(~PORT_W_CLK_POL)) _TECHMAP_REPLACE_ (.WCK(PORT_W_CLK), .I(PORT_W_WR_DATA), .RA(PORT_R_ADDR), .WA(PORT_W_ADDR), .WE(PORT_W_WR_EN), .WEA(1'b1), .O(PORT_R_RD_DATA));
endmodule
