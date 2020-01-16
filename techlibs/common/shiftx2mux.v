(* techmap_celltype = /*"$shift*/ "$shiftx" *)
module _80_shift_shiftx (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

    parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
    parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

    generate
        genvar i;
        localparam CLOG2_Y_WIDTH = $clog2(Y_WIDTH);

        if (B_WIDTH <= CLOG2_Y_WIDTH+1)
            wire _TECHMAP_FAIL_ = 1;
        // In order to perform this optimisation, this $shiftx must
        //   only shift in units of Y_WIDTH, which we check by ensuring
        //   that the appropriate LSBs of B are zero
        else if (_TECHMAP_CONSTMSK_B_[CLOG2_Y_WIDTH-1:0] == {CLOG2_Y_WIDTH{1'b1}} && _TECHMAP_CONSTVAL_B_[CLOG2_Y_WIDTH-1:0] != {CLOG2_Y_WIDTH{1'b0}})
            wire _TECHMAP_FAIL_ = 1;
        else begin
            // Halve the size of $shiftx by $mux-ing A according to 
            //   the LSB of B, after discarding the zeroed bits
            wire [(A_WIDTH+Y_WIDTH)/2-1:0] AA;
            for (i = 0; i < (A_WIDTH/Y_WIDTH); i=i+2)
                assign AA[(i/2)*Y_WIDTH +: Y_WIDTH] = B[CLOG2_Y_WIDTH] ? A[(i+1)*Y_WIDTH +: Y_WIDTH] : A[(i+0)*Y_WIDTH +: Y_WIDTH];
            $shiftx #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH((A_WIDTH+Y_WIDTH)/2'd2), .B_WIDTH(B_WIDTH-1), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(AA), .B({B[B_WIDTH-1:CLOG2_Y_WIDTH+1], {CLOG2_Y_WIDTH{1'b0}}}), .Y(Y));
        end
    endgenerate
endmodule


