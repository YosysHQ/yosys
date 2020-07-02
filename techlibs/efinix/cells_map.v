(* techmap_celltype = "$_DFFE_PP0P_ $_DFFE_PP0N_ $_DFFE_PP1P_ $_DFFE_PP1N_ $_DFFE_PN0P_ $_DFFE_PN0N_ $_DFFE_PN1P_ $_DFFE_PN1N_ $_DFFE_NP0P_ $_DFFE_NP0N_ $_DFFE_NP1P_ $_DFFE_NP1N_ $_DFFE_NN0P_ $_DFFE_NN0N_ $_DFFE_NN1P_ $_DFFE_NN1N_" *)
module  \$_DFFE_xxxx_ (input D, C, R, E, output Q);

  parameter _TECHMAP_CELLTYPE_ = "";

  EFX_FF #(
    .CLK_POLARITY(_TECHMAP_CELLTYPE_[39:32] == "P"),
    .CE_POLARITY(_TECHMAP_CELLTYPE_[15:8] == "P"),
    .SR_POLARITY(_TECHMAP_CELLTYPE_[31:24] == "P"),
    .D_POLARITY(1'b1),
    .SR_SYNC(1'b0),
    .SR_VALUE(_TECHMAP_CELLTYPE_[23:16] == "1"),
    .SR_SYNC_PRIORITY(1'b1)
  ) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(R), .Q(Q));

  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;

endmodule

(* techmap_celltype = "$_SDFFE_PP0P_ $_SDFFE_PP0N_ $_SDFFE_PP1P_ $_SDFFE_PP1N_ $_SDFFE_PN0P_ $_SDFFE_PN0N_ $_SDFFE_PN1P_ $_SDFFE_PN1N_ $_SDFFE_NP0P_ $_SDFFE_NP0N_ $_SDFFE_NP1P_ $_SDFFE_NP1N_ $_SDFFE_NN0P_ $_SDFFE_NN0N_ $_SDFFE_NN1P_ $_SDFFE_NN1N_" *)
module  \$_SDFFE_xxxx_ (input D, C, R, E, output Q);

  parameter _TECHMAP_CELLTYPE_ = "";

  EFX_FF #(
    .CLK_POLARITY(_TECHMAP_CELLTYPE_[39:32] == "P"),
    .CE_POLARITY(_TECHMAP_CELLTYPE_[15:8] == "P"),
    .SR_POLARITY(_TECHMAP_CELLTYPE_[31:24] == "P"),
    .D_POLARITY(1'b1),
    .SR_SYNC(1'b1),
    .SR_VALUE(_TECHMAP_CELLTYPE_[23:16] == "1"),
    .SR_SYNC_PRIORITY(1'b1)
  ) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(R), .Q(Q));

  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;

endmodule

(* techmap_celltype = "$_SDFFCE_PP0P_ $_SDFFCE_PP0N_ $_SDFFCE_PP1P_ $_SDFFCE_PP1N_ $_SDFFCE_PN0P_ $_SDFFCE_PN0N_ $_SDFFCE_PN1P_ $_SDFFCE_PN1N_ $_SDFFCE_NP0P_ $_SDFFCE_NP0N_ $_SDFFCE_NP1P_ $_SDFFCE_NP1N_ $_SDFFCE_NN0P_ $_SDFFCE_NN0N_ $_SDFFCE_NN1P_ $_SDFFCE_NN1N_" *)
module  \$_SDFFCE_xxxx_ (input D, C, R, E, output Q);

  parameter _TECHMAP_CELLTYPE_ = "";

  EFX_FF #(
    .CLK_POLARITY(_TECHMAP_CELLTYPE_[39:32] == "P"),
    .CE_POLARITY(_TECHMAP_CELLTYPE_[15:8] == "P"),
    .SR_POLARITY(_TECHMAP_CELLTYPE_[31:24] == "P"),
    .D_POLARITY(1'b1),
    .SR_SYNC(1'b1),
    .SR_VALUE(_TECHMAP_CELLTYPE_[23:16] == "1"),
    .SR_SYNC_PRIORITY(1'b0)
  ) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(R), .Q(Q));

  wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;

endmodule

module \$_DLATCH_N_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = !E ? D : Q;
endmodule

module \$_DLATCH_P_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = E ? D : Q;
endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(1'b0), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 2) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 3) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(1'b0));
    end else
    if (WIDTH == 4) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
