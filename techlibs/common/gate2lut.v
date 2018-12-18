(* techmap_celltype = "$_NOT_" *)
module _90_lut_not (A, Y);
    input A;
    output Y;

    wire [`LUT_WIDTH-1:0] AA;
    assign AA = {A};

    \$lut #(
        .WIDTH(`LUT_WIDTH),
        .LUT(4'b01)
    ) lut (
        .A(AA),
        .Y(Y)
    );
endmodule

(* techmap_celltype = "$_OR_" *)
module _90_lut_or (A, B, Y);
    input A, B;
    output Y;

    wire [`LUT_WIDTH-1:0] AA;
    assign AA = {B, A};

    \$lut #(
        .WIDTH(`LUT_WIDTH),
        .LUT(4'b1110)
    ) lut (
        .A(AA),
        .Y(Y)
    );
endmodule

(* techmap_celltype = "$_AND_" *)
module _90_lut_and (A, B, Y);
    input A, B;
    output Y;

    wire [`LUT_WIDTH-1:0] AA;
    assign AA = {B, A};

    \$lut #(
        .WIDTH(`LUT_WIDTH),
        .LUT(4'b1000)
    ) lut (
        .A(AA),
        .Y(Y)
    );
endmodule

(* techmap_celltype = "$_XOR_" *)
module _90_lut_xor (A, B, Y);
    input A, B;
    output Y;

    wire [`LUT_WIDTH-1:0] AA;
    assign AA = {B, A};

    \$lut #(
        .WIDTH(`LUT_WIDTH),
        .LUT(4'b0110)
    ) lut (
        .A(AA),
        .Y(Y)
    );
endmodule

(* techmap_celltype = "$_MUX_" *)
module _90_lut_mux (A, B, S, Y);
    input A, B, S;
    output Y;

    wire [`LUT_WIDTH-1:0] AA;
    assign AA = {S, B, A};

    \$lut #(
        .WIDTH(`LUT_WIDTH),
        //     A 1010 1010
        //     B 1100 1100
        //     S 1111 0000
        .LUT(8'b_1100_1010)
    ) lut (
        .A(AA),
        .Y(Y)
    );
endmodule
