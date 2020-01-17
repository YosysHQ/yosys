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
localparam gt_width = `LUT_WIDTH/2;

generate
    if (_TECHMAP_CELLTYPE_ == "" || (A_WIDTH <= gt_width || B_WIDTH <= gt_width))
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

        // Compute width of $lcu/carry-chain cell
        localparam lcu_width = (WIDTH+gt_width-1)/gt_width;
        wire [lcu_width-1:0] P, G, CO;
        genvar i, j;
        integer j;
        for (i = 0; i < WIDTH; i=i+gt_width) begin
            wire [gt_width-1:0] PP, GG;
            if (i < WIDTH-gt_width) begin
                // Bit-wise equality (xnor) of sign-extended A and B
                assign PP = AA[i +: gt_width] ^~ BB[i +: gt_width];
                // Priority "encoder" that checks A[i] == 1'b1 && B[i] == 1'b0
                //   from MSB down, deferring to less significant bits if the
                //   MSBs are equal
                assign GG[gt_width-1] = AA[i+gt_width-1] & ~BB[i+gt_width-1];
                for (j = gt_width-2; j >= 0; j=j-1)
                    assign GG[j] = &PP[gt_width-1:j+1] & (AA[i+j] & ~BB[i+j]);
                // Propagate only if all bits are equal
                //   (inconclusive evidence to say A >= B)
                assign P[i/gt_width] = &PP;
                // Generate if any pairs call for it
                assign G[i/gt_width] = |GG;
            end
            else begin
                assign PP = AA[WIDTH-1:i] ^~ BB[WIDTH-1:i];
                if (A_SIGNED && B_SIGNED)
                    assign GG[WIDTH-i-1] = ~AA[WIDTH-1] & BB[WIDTH-1];
                else
                    assign GG[WIDTH-i-1] = AA[WIDTH-1] & ~BB[WIDTH-1];
                for (j = WIDTH-i-2; j >= 0; j=j-1)
                    assign GG[j] = &PP[WIDTH-i-1:j+1] & (AA[i+j] & ~BB[i+j]);
                assign P[i/gt_width] = &PP[WIDTH-i-1:0];
                assign G[i/gt_width] = |GG[WIDTH-i-1:0];
            end
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
