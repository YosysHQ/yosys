module \$lut (A, Y);

parameter WIDTH = 1;
parameter LUT = 0;

(* force_downto *)
input [WIDTH-1:0] A;
output Y;

generate
    if (WIDTH == 1) begin
        generate
            if (LUT == 2'b00) begin
                assign Y = 1'b0;
            end
            else if (LUT == 2'b01) begin
                MISTRAL_NOT _TECHMAP_REPLACE_(
                    .A(A[0]), .Q(Y)
                );
            end
            else if (LUT == 2'b10) begin
                assign Y = A;
            end
            else if (LUT == 2'b11) begin
                assign Y = 1'b1;
            end
        endgenerate
    end else
    if (WIDTH == 2) begin
        MISTRAL_ALUT2 #(.LUT(LUT)) _TECHMAP_REPLACE_(
            .A(A[0]), .B(A[1]), .Q(Y)
        );
    end else
    if (WIDTH == 3) begin
        MISTRAL_ALUT3 #(.LUT(LUT)) _TECHMAP_REPLACE_(
            .A(A[0]), .B(A[1]), .C(A[2]), .Q(Y)
        );
    end else
    if (WIDTH == 4) begin
        MISTRAL_ALUT4 #(.LUT(LUT)) _TECHMAP_REPLACE_(
            .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]), .Q(Y)
        );
    end else
    if (WIDTH == 5) begin
        MISTRAL_ALUT5 #(.LUT(LUT)) _TECHMAP_REPLACE_ (
            .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]), .E(A[4]), .Q(Y)
        );
    end else
    if (WIDTH == 6) begin
        MISTRAL_ALUT6 #(.LUT(LUT)) _TECHMAP_REPLACE_ (
            .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]), .E(A[4]), .F(A[5]), .Q(Y)
        );
    end else begin
        wire _TECHMAP_FAIL_ = 1'b1;
    end
endgenerate
endmodule
