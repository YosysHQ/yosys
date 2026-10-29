// $alu -> LE carry chain. Each LE adds one bit: DATAA = A, DATAB = B,
// CIN = carry in; the upper half of the mask (DATAD tied to 1) is
// the sum, the lower half (what COUT always uses, DATAD = 0) the carry.
// A constant carry-in is folded into bit 0, whose mask then ignores C so
// the chain head's hardware carry-in doesn't matter; a signal carry-in
// gets one extra LE in front. The carry out of the top bit leaves the
// chain through one extra LE (COMBOUT = CIN); the other carry outs are
// recovered from the sums.

(* techmap_celltype = "$alu" *)
module _80_cy2_alu (A, B, CI, BI, X, Y, CO);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  (* force_downto *) input [A_WIDTH-1:0] A;
  (* force_downto *) input [B_WIDTH-1:0] B;
  (* force_downto *) output [Y_WIDTH-1:0] X, Y;
  input CI, BI;
  (* force_downto *) output [Y_WIDTH-1:0] CO;

  // Short adders are cheaper as plain LUTs.
  wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

  parameter _TECHMAP_CONSTMSK_CI_ = 0;
  parameter _TECHMAP_CONSTVAL_CI_ = 0;
  parameter _TECHMAP_CONSTMSK_BI_ = 0;
  parameter _TECHMAP_CONSTVAL_BI_ = 0;

  (* force_downto *) wire [Y_WIDTH-1:0] A_buf, B_buf;
  \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
  \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

  // B inversion folds into the masks when BI is constant.
  localparam INV_B = _TECHMAP_CONSTMSK_BI_ && _TECHMAP_CONSTVAL_BI_;
  wire [Y_WIDTH-1:0] BB = _TECHMAP_CONSTMSK_BI_ ? B_buf : (BI ? ~B_buf : B_buf);
  wire [Y_WIDTH-1:0] BX = INV_B ? ~B_buf : BB;

  // mode 0: C from CIN; 1/2: carry in is the constant 0/1.
  function [15:0] lcmask(input integer mode, input integer inv_b);
    integer idx;
    reg a, b, c, d;
    begin
      for (idx = 0; idx < 16; idx = idx + 1) begin
        a = idx & 1;
        b = ((idx >> 1) & 1) ^ inv_b;
        c = mode == 0 ? ((idx >> 2) & 1) : mode == 2;
        d = (idx >> 3) & 1;
        lcmask[idx] = d ? (a ^ b ^ c) : ((a & b) | (a & c) | (b & c));
      end
    end
  endfunction

  localparam CI_CONST = _TECHMAP_CONSTMSK_CI_;
  localparam HEAD_MODE = CI_CONST ? (_TECHMAP_CONSTVAL_CI_ ? 2 : 1) : 0;

  (* force_downto *) wire [Y_WIDTH:0] C;
  generate
    if (!CI_CONST)
      LCELL_COMB #(.LUT_MASK(16'h00AA)) carry_in (.DATAA(CI), .DATAB(1'b1), .DATAC(1'b1), .DATAD(1'b1),
        .CIN(1'b1), .COUT(C[0]));
  endgenerate

  genvar i;
  generate
    for (i = 0; i < Y_WIDTH; i = i + 1) begin : bit
      if (i == 0 && CI_CONST)
        LCELL_COMB #(.LUT_MASK(lcmask(HEAD_MODE, INV_B))) lc (
          .DATAA(A_buf[i]), .DATAB(BB[i]), .DATAC(1'b1), .DATAD(1'b1), .CIN(1'b1),
          .COMBOUT(Y[i]), .COUT(C[i+1]));
      else
        LCELL_COMB #(.LUT_MASK(lcmask(0, INV_B))) lc (
          .DATAA(A_buf[i]), .DATAB(BB[i]), .DATAC(1'b1), .DATAD(1'b1), .CIN(C[i]),
          .COMBOUT(Y[i]), .COUT(C[i+1]));
    end
  endgenerate

  wire top_carry;
  LCELL_COMB #(.LUT_MASK(16'hF000)) carry_out (.DATAA(1'b1), .DATAB(1'b1), .DATAC(1'b1), .DATAD(1'b1),
    .CIN(C[Y_WIDTH]), .COMBOUT(top_carry));

  assign X = A_buf ^ BX;
  generate
    if (Y_WIDTH > 1)
      assign CO = {top_carry, Y[Y_WIDTH-1:1] ^ X[Y_WIDTH-1:1]};
    else
      assign CO = top_carry;
  endgenerate
endmodule
