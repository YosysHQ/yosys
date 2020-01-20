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
    else if (A_WIDTH != B_WIDTH) begin
        // Perform sign extension on A and B
        localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;
        wire [WIDTH-1:0] AA = {{(WIDTH-A_WIDTH){A_SIGNED ? A[A_WIDTH-1] : 1'b0}}, A};
        wire [WIDTH-1:0] BB = {{(WIDTH-B_WIDTH){B_SIGNED ? B[B_WIDTH-1] : 1'b0}}, B};
        if (_TECHMAP_CELLTYPE_ == "$gt")
            $gt #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(WIDTH), .B_WIDTH(WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(AA), .B(BB), .Y(Y));
        else if (_TECHMAP_CELLTYPE_ == "$ge")
            $ge #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(WIDTH), .B_WIDTH(WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(AA), .B(BB), .Y(Y));
        else
            wire _TECHMAP_FAIL_ = 1;
    end
    else begin
        localparam cmp_width = `LUT_WIDTH/2;
        localparam lcu_width = (A_WIDTH+cmp_width-1)/cmp_width;
        wire [lcu_width-1:0] P, G, CO;
        genvar i, j;
        for (i = 0; i < A_WIDTH; i=i+cmp_width) begin
            wire [cmp_width-1:0] PP, GG;
            for (j = cmp_width-1; j >= 0 && i+j < A_WIDTH; j = j-1) begin
                // Bit-wise equality (xnor) of sign-extended A and B
                assign PP[j] = A[i+j] ^~ B[i+j];
                if (i+j == A_WIDTH-1 && A_SIGNED && B_SIGNED)
                    assign GG[j] = ~A[i+j] & B[i+j];
                else if (j == cmp_width-1)
                    assign GG[j] = A[i+j] & ~B[i+j];
                else
                    // Priority "encoder" that checks A[i] == 1'b1 && B[i] == 1'b0
                    //   from MSB down, deferring to less significant bits if the
                    //   MSBs are equal
                    assign GG[j] = &PP[cmp_width-1:j+1] & (A[i+j] & ~B[i+j]);
            end
            // Propagate only if all bit pairs are equal
            //   (inconclusive evidence to say A >= B)
            assign P[i/cmp_width] = &PP;
            // Generate if any bit pairs call for it
            assign G[i/cmp_width] = |GG;
        end
        // For $ge operation, start with the assumption that A and B are
        //   equal (propagating this equality if A and B turn out to be so)
        if (_TECHMAP_CELLTYPE_ == "$ge")
            wire CI = 1'b1;
        else
            wire CI = 1'b0;
        $lcu #(.WIDTH(lcu_width)) lcu (.P(P), .G(G), .CI(CI), .CO(CO));
        assign Y = CO[lcu_width-1];
    end
endgenerate
endmodule
