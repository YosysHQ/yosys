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

module \$_DFFE_NN_ (D, Q, C, E);
    input  D;
    output Q;
    input  C;
    input  E;

    wire C_INV;
    \$_NOT_ clkinv (.Y(C_INV), .A(C));
    wire E_INV;
    \$_NOT_ enainv (.Y(E_INV), .A(E));

    dffe _TECHMAP_REPLACE_ (.CLK(C_INV), .D(D), .EN(E_INV), .Q(Q));
endmodule

module \$_DFFE_NP_ (D, Q, C, E);
    input  D;
    output Q;
    input  C;
    input  E;

    wire C_INV;
    \$_NOT_ clkinv (.Y(C_INV), .A(C));

    dffe _TECHMAP_REPLACE_ (.CLK(C_INV), .D(D), .EN(E), .Q(Q));
endmodule

module \$_DFFE_PN_ (D, Q, C, E);
    input  D;
    output Q;
    input  C;
    input  E;

    wire E_INV;
    \$_NOT_ enainv (.Y(E_INV), .A(E));

    dffe _TECHMAP_REPLACE_ (.CLK(C), .D(D), .EN(E_INV), .Q(Q));
endmodule

module \$_DFFE_PP_ (D, Q, C, E);
    input  D;
    output Q;
    input  C;
    input  E;

    dffe _TECHMAP_REPLACE_ (.CLK(C), .D(D), .EN(E), .Q(Q));
endmodule
