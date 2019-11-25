module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    function [WIDTH ** 2 - 1:0] INIT_address_inverse;
        input [WIDTH ** 2 - 1: 0] arr;
        integer i;
        integer n;
        reg [WIDTH - 1:0] tmp;
        reg [WIDTH - 1:0] tmp2;
        tmp = 0;
        tmp2 = 0;
        for (i = 0; i < WIDTH ** 2; i++) begin
            INIT_address_inverse[tmp2] = arr[tmp];
            tmp = tmp + 1;
            for (n = 0; n < WIDTH; n++) begin
                tmp2[WIDTH - 1 - n] = tmp[n];
            end
        end
    endfunction

    generate
        if (WIDTH == 1)
        begin
            LUT1 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]));
        end
        else if (WIDTH == 2)
        begin
            LUT2 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[1]), .I1(A[0]));
        end
        else if (WIDTH == 3)
        begin
            LUT3 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[2]), .I1(A[1]), .I2(A[0]));
        end
        else if (WIDTH == 4)
        begin
            LUT4 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[3]), .I1(A[2]), .I2(A[1]), .I3(A[0]));
        end
        else
        begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule

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

module \$_DFF_N_ (D, Q, C);
    input D;
    input C;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    dff tmpdff (.Q(Q), .D(D), .CLK(C_INV));
endmodule

module \$_DFF_P_ (D, Q, C);
    input D;
    input C;
    output Q;
    dff _TECHMAP_REPLACE_ (.Q(Q), .D(D), .CLK(C));
endmodule

module \$_DFF_NN0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    wire R_INV;
    inv clrinv (.Q(R_INV), .A(R));
    dffc tmpdffc (.Q(Q), .D(D), .CLK(C_INV), .CLR(R_INV));
endmodule

module \$_DFF_NN1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    wire R_INV;
    inv preinv (.Q(R_INV), .A(R));
    dffp tmpdffp (.Q(Q), .D(D), .CLK(C_INV), .PRE(R_INV));
endmodule

module \$_DFF_NP0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    dffc tmpdffc (.Q(Q), .D(D), .CLK(C_INV), .CLR(R));
endmodule

module \$_DFF_NP1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    dffp tmpdffp (.Q(Q), .D(D), .CLK(C_INV), .PRE(R));
endmodule

module \$_DFF_PN0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire R_INV;
    inv preinv (.Q(R_INV), .A(R));
    dffc tmpdffc (.Q(Q), .D(D), .CLK(C), .CLR(R_INV));
endmodule

module \$_DFF_PN1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    wire R_INV;
    inv preinv (.Q(R_INV), .A(R));
    dffp tmpdffp (.Q(Q), .D(D), .CLK(C), .PRE(R_INV));
endmodule

module \$_DFF_PP0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    dffc _TECHMAP_REPLACE_ (.Q(Q), .D(D), .CLK(C), .CLR(R));
endmodule

module \$_DFF_PP1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    dffp _TECHMAP_REPLACE_ (.Q(Q), .D(D), .CLK(C), .PRE(R));
endmodule

module \$_DFFSR_NPP_ (D, Q, C, R, S);
    input D;
    input C;
    input R;
    input S;
    output Q;
    wire C_INV;
    inv clkinv (.Q(C_INV), .A(C));
    dffpc tmpdffpc (.Q(Q), .D(D), .CLK(C_INV), .CLR(R), .PRE(S));
endmodule

module \$_DFFSR_PPP_ (D, Q, C, R, S);
    input D;
    input C;
    input R;
    input S;
    output Q;
    dffpc tmpdffpc (.Q(Q), .D(D), .CLK(C), .CLR(R), .PRE(S));
endmodule

module \$_DLATCH_P_ (E, D, Q);
    input E;
    input D;
    output reg Q;
    LUT3 #(.INIT(8'b11100010)) latchimpl (.O(Q), .I2(D), .I1(E), .I0(Q));
endmodule

module \$_DLATCH_N_ (E, D, Q);
    input E;
    input D;
    output reg Q;
    LUT3 #(.INIT(8'b10111000)) latchimpl (.O(Q), .I2(D), .I1(E), .I0(Q));
endmodule

module \$_DLATCHSR_NNN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b101011001111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NNP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b101011001111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NPN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111010110)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NPP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111010110)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PNN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b110010101111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PNP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b110010101111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PPN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111100101)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PPP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b11111111110010)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
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
