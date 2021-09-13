// This pass performs an optimisation that decomposes wide arithmetic
//   comparisons into LUT-size chunks (as guided by the `LUT_WIDTH
//   macro) connected to a single lookahead-carry-unit $lcu cell,
//   which is typically mapped to dedicated (and fast) FPGA
//   carry-chains.
(* techmap_celltype = "$lt $le $gt $ge" *)
module _80_lcu_cmp_ (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;
parameter Y_WIDTH = 0;

(* force_downto *)
input [A_WIDTH-1:0] A;
(* force_downto *)
input [B_WIDTH-1:0] B;
(* force_downto *)
output [Y_WIDTH-1:0] Y;

parameter _TECHMAP_CELLTYPE_ = "";

generate
    if (_TECHMAP_CELLTYPE_ == "" || `LUT_WIDTH < 2)
        wire _TECHMAP_FAIL_ = 1;
    else if (_TECHMAP_CELLTYPE_ == "$lt") begin
        // Transform $lt into $gt by swapping A and B
        $gt #(.A_SIGNED(B_SIGNED), .B_SIGNED(A_SIGNED), .A_WIDTH(B_WIDTH), .B_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(B), .B(A), .Y(Y));
    end
    else if (_TECHMAP_CELLTYPE_ == "$le") begin
        // Transform $le into $ge by swapping A and B
        $ge #(.A_SIGNED(B_SIGNED), .B_SIGNED(A_SIGNED), .A_WIDTH(B_WIDTH), .B_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(B), .B(A), .Y(Y));
    end
    else begin
        // Perform sign extension on A and B
        localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;
        (* force_downto *)
        wire [WIDTH-1:0] AA = {{(WIDTH-A_WIDTH){A_SIGNED ? A[A_WIDTH-1] : 1'b0}}, A};
        (* force_downto *)
        wire [WIDTH-1:0] BB = {{(WIDTH-B_WIDTH){B_SIGNED ? B[B_WIDTH-1] : 1'b0}}, B};
        // For $ge operation, start with the assumption that A and B are
        //   equal (propagating this equality if A and B turn out to be so)
        localparam CI = _TECHMAP_CELLTYPE_ == "$ge";
        $__CMP2LCU #(.AB_WIDTH(WIDTH), .AB_SIGNED(A_SIGNED && B_SIGNED), .LCU_WIDTH(1), .BUDGET(`LUT_WIDTH), .CI(CI))
            _TECHMAP_REPLACE_ (.A(AA), .B(BB), .P(1'b1), .G(1'b0), .Y(Y));
    end
endgenerate
endmodule

module $__CMP2LCU (A, B, P, G, Y);

parameter AB_WIDTH = 0;
parameter AB_SIGNED = 0;
parameter LCU_WIDTH = 1;
parameter BUDGET = 0;
parameter CI = 0;

(* force_downto *)
input [AB_WIDTH-1:0] A; // A from original $gt/$ge
(* force_downto *)
input [AB_WIDTH-1:0] B; // B from original $gt/$ge
(* force_downto *)
input [LCU_WIDTH-1:0] P; // P of $lcu
(* force_downto *)
input [LCU_WIDTH-1:0] G; // G of $lcu
output Y;

parameter [AB_WIDTH-1:0] _TECHMAP_CONSTMSK_A_ = 0;
parameter [AB_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
parameter [LCU_WIDTH-1:0] _TECHMAP_CONSTMSK_P_ = 0;

generate
    if (AB_WIDTH == 0) begin
        (* force_downto *)
        wire [LCU_WIDTH-1:0] CO;
        $lcu #(.WIDTH(LCU_WIDTH)) _TECHMAP_REPLACE_ (.P(P), .G(G), .CI(CI), .CO(CO));
        assign Y = CO[LCU_WIDTH-1];
    end
    else begin
        localparam COST =
            _TECHMAP_CONSTMSK_A_[AB_WIDTH-1:0] && _TECHMAP_CONSTMSK_B_[AB_WIDTH-1:0]
            ? 0
            : (_TECHMAP_CONSTMSK_A_[AB_WIDTH-1:0] || _TECHMAP_CONSTMSK_B_[AB_WIDTH-1:0]
                ? 1
                : 2);

        if (BUDGET < COST)
             $__CMP2LCU #(.AB_WIDTH(AB_WIDTH), .AB_SIGNED(AB_SIGNED), .LCU_WIDTH(LCU_WIDTH+1), .BUDGET(`LUT_WIDTH), .CI(CI))
                _TECHMAP_REPLACE_ (.A(A), .B(B), .P({P, 1'b1}), .G({G, 1'b0}), .Y(Y));
        else begin
            wire PP, GG;
            // Bit-wise equality (xnor) of A and B
            assign PP = A[AB_WIDTH-1] ^~ B[AB_WIDTH-1];
            if (AB_SIGNED)
                assign GG = ~A[AB_WIDTH-1] & B[AB_WIDTH-1];
            else if (_TECHMAP_CONSTMSK_P_[LCU_WIDTH-1]) // First compare for LUT if P (and G) is constant
                assign GG = A[AB_WIDTH-1] & ~B[AB_WIDTH-1];
            else
                // Priority "encoder" that checks A[i] == 1'b1 && B[i] == 1'b0
                //   from MSB down, deferring to less significant bits if the
                //   MSBs are equal
                assign GG = P[0] & (A[AB_WIDTH-1] & ~B[AB_WIDTH-1]);
            (* force_downto *)
            wire [LCU_WIDTH-1:0] P_, G_;
            if (LCU_WIDTH == 1) begin
                // Propagate only if all pairs are equal
                //   (inconclusive evidence to say A >= B)
                assign P_ = P[0] & PP;
                // Generate if any comparisons call for it
                assign G_ = G[0] | GG;
            end
            else begin
                // Propagate only if all pairs are equal
                //   (inconclusive evidence to say A >= B)
                assign P_ = {P[LCU_WIDTH-1:1], P[0] & PP};
                // Generate if any comparisons call for it
                assign G_ = {G[LCU_WIDTH-1:1], G[0] | GG};
            end
            if (AB_WIDTH == 1)
               $__CMP2LCU #(.AB_WIDTH(AB_WIDTH-1), .AB_SIGNED(1'b0), .LCU_WIDTH(LCU_WIDTH), .BUDGET(BUDGET-COST), .CI(CI))
                    _TECHMAP_REPLACE_ (.A(), .B(), .P(P_), .G(G_), .Y(Y));
            else
               $__CMP2LCU #(.AB_WIDTH(AB_WIDTH-1), .AB_SIGNED(1'b0), .LCU_WIDTH(LCU_WIDTH), .BUDGET(BUDGET-COST), .CI(CI))
                    _TECHMAP_REPLACE_ (.A(A[AB_WIDTH-2:0]), .B(B[AB_WIDTH-2:0]), .P(P_), .G(G_), .Y(Y));
        end
    end
endgenerate
endmodule
