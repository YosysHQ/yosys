
module \$_MUX8_ (A, B, C, D, E, F, G, H, S, T, U, Y);
    input A, B, C, D, E, F, G, H, S, T, U;
    output Y;
    mux8x0 _TECHMAP_REPLACE_ (.A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G), .H(H), .S0(S), .S1(T), .S2(U), .Q(Y));
endmodule

module \$_MUX4_ (A, B, C, D, S, T, U, Y);
    input A, B, C, D, S, T, U;
    output Y;
    mux4x0 _TECHMAP_REPLACE_ (.A(A), .B(B), .C(C), .D(D), .S0(S), .S1(T), .Q(Y));
endmodule

module qlal4s3_mult_16x16_cell (
    input [15:0] Amult,
    input [15:0] Bmult,
    input [1:0] Valid_mult,
    input [31:0] Cmult);

    wire [63:0] Cmult_w;
    wire [31:0] Amult_w;
    wire [31:0] Bmult_w;
    wire [1:0] Valid_mult;

    assign Amult_w = {{16{Amult[15]}}, Amult};
    assign Bmult_w = {{16{Bmult[15]}}, Bmult};
    assign Cmult = Cmult_w[31:0];
    assign Valid_mult_w = {1'b0, Valid_mult[0]};

    qlal4s3_mult_32x32_cell I1 ( .Amult(Amult_w), .Bmult(Bmult_w), .Cmult(Cmult_w), .Valid_mult(Valid_mult_w));
endmodule
