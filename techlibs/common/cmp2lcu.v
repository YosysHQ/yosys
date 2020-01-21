// This pass performs an optimisation that decomposes wide arithmetic
//   comparisons into LUT-size chunks (as guided by the `LUT_WIDTH
//   macro) connected to a single lookahead-carry-unit $lcu cell,
//   which is typically mapped to dedicated (and fast) FPGA
//   carry-chains.
(* techmap_celltype = "$lt $le $gt $ge" *)
module _90_lcu_cmp_ (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;
parameter Y_WIDTH = 0;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

parameter _TECHMAP_CELLTYPE_ = "";

generate
    if (_TECHMAP_CELLTYPE_ == "")
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
        wire [WIDTH-1:0] AA = {{(WIDTH-A_WIDTH){A_SIGNED ? A[A_WIDTH-1] : 1'b0}}, A};
        wire [WIDTH-1:0] BB = {{(WIDTH-B_WIDTH){B_SIGNED ? B[B_WIDTH-1] : 1'b0}}, B};
        // For $ge operation, start with the assumption that A and B are
        //   equal (propagating this equality if A and B turn out to be so)
        if (_TECHMAP_CELLTYPE_ == "$ge")
            localparam CI = 1'b1;
        else
            localparam CI = 1'b0;
        $__CMP2LCU #(.AB_WIDTH(WIDTH), .AB_SIGNED(A_SIGNED && B_SIGNED), .LCU_WIDTH(0), .BUDGET(`LUT_WIDTH), .CI(CI))
            _TECHMAP_REPLACE_ (.A(AA), .B(BB), .P(), .G(), .PP(1'b1), .GG(1'b0), .Y(Y));
    end
endgenerate
endmodule

module $__CMP2LCU (A, B, P, G, PP, GG, Y);

parameter AB_WIDTH = 0;
parameter AB_SIGNED = 0;
parameter LCU_WIDTH = 0;
parameter BUDGET = 0;
parameter CI = 0;

input [AB_WIDTH-1:0] A;
input [AB_WIDTH-1:0] B;
input [LCU_WIDTH-1:0] P;
input [LCU_WIDTH-1:0] G;
input PP;
input GG;
output Y;

parameter [AB_WIDTH-1:0] _TECHMAP_CONSTMSK_A_ = 0;
parameter [AB_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;

generate
    if (AB_WIDTH == 0) begin
        if (BUDGET < `LUT_WIDTH)
             $__CMP2LCU #(.AB_WIDTH(AB_WIDTH), .AB_SIGNED(AB_SIGNED), .LCU_WIDTH(LCU_WIDTH+1), .BUDGET(`LUT_WIDTH), .CI(CI))
                _TECHMAP_REPLACE_ (.A(A), .B(B), .P({P, PP}), .G({G, GG}), .PP(1'b1), .GG(1'b0), .Y(Y));
        else begin
            wire [LCU_WIDTH-1:0] CO;
            $lcu #(.WIDTH(LCU_WIDTH)) _TECHMAP_REPLACE_ (.P(P), .G(G), .CI(CI), .CO(CO));
            assign Y = CO[LCU_WIDTH-1];
        end
    end
    else begin
        if (BUDGET < 2)
             $__CMP2LCU #(.AB_WIDTH(AB_WIDTH), .AB_SIGNED(AB_SIGNED), .LCU_WIDTH(LCU_WIDTH+1), .BUDGET(`LUT_WIDTH), .CI(CI))
                _TECHMAP_REPLACE_ (.A(A), .B(B), .P({P, PP}), .G({G, GG}), .PP(1'b1), .GG(1'b0), .Y(Y));
        else begin
            wire PPP, GGG;
            // Bit-wise equality (xnor) of A and B
            assign PPP = A[AB_WIDTH-1] ^~ B[AB_WIDTH-1];
            if (AB_SIGNED)
                assign GGG = ~A[AB_WIDTH-1] & B[AB_WIDTH-1];
            else if (BUDGET == `LUT_WIDTH)
                assign GGG = A[AB_WIDTH-1] & ~B[AB_WIDTH-1];
            else
                // Priority "encoder" that checks A[i] == 1'b1 && B[i] == 1'b0
                //   from MSB down, deferring to less significant bits if the
                //   MSBs are equal
                assign GGG = PP & (A[AB_WIDTH-1] & ~B[AB_WIDTH-1]);
            $__CMP2LCU #(.AB_WIDTH(AB_WIDTH-1), .AB_SIGNED(1'b0), .LCU_WIDTH(LCU_WIDTH), .BUDGET(BUDGET-2), .CI(CI))
                _TECHMAP_REPLACE_ (.A(A[AB_WIDTH-2:0]), .B(B[AB_WIDTH-2:0]), .P(P), .G(G), 
                // Propagate only if all bit pairs are equal
                //   (inconclusive evidence to say A >= B)
                .PP(PP & PPP), 
                // Generate if any bit pairs call for it
                .GG(GG | GGG),
                .Y(Y));
        end
    end
endgenerate
endmodule
