// Rising edge DFF
module \$_DFF_P_ (D, C, Q);
    input D;
    input C;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dff _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C));
endmodule

// Rising edge DFF with async active-high reset
module \$_DFF_PP0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffr _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .R(R));
endmodule

// Rising edge DFF with async active-high set
module \$_DFF_PP1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffs _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .S(R));
endmodule

// Rising edge DFF with async active-low reset
module \$_DFF_PN0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffrn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .RN(R));
endmodule

// Rising edge DFF with async active-low set
module \$_DFF_PN1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffsn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .SN(R));
endmodule

// Rising edge DFF with sync active-high reset
module \$_SDFF_PP0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffr _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .R(R));
endmodule

// Rising edge DFF with sync active-high set
module \$_SDFF_PP1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffs _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .S(R));
endmodule

// Rising edge DFF with sync active-low reset
module \$_SDFF_PN0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffrn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .RN(R));
endmodule

// Rising edge DFF with sync active-low set
module \$_SDFF_PN1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffsn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .SN(R));
endmodule

// Falling edge DFF
module \$_DFF_N_ (D, C, Q);
    input D;
    input C;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C));
endmodule

// Falling edge DFF with async active-high reset
module \$_DFF_NP0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffnr _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .R(R));
endmodule

// Falling edge DFF with async active-high set
module \$_DFF_NP1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffns _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .S(R));
endmodule

// Falling edge DFF with async active-low reset
module \$_DFF_NN0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffnrn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .RN(R));
endmodule

// Falling edge DFF with async active-low set
module \$_DFF_NN1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    dffnsn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .SN(R));
endmodule

// Falling edge DFF with sync active-high reset
module \$_SDFF_NP0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffnr _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .R(R));
endmodule

// Falling edge DFF with sync active-high set
module \$_SDFF_NP1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffns _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .S(R));
endmodule

// Falling edge DFF with sync active-low reset
module \$_SDFF_NN0_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffnrn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .RN(R));
endmodule

// Falling edge DFF with sync active-low set
module \$_SDFF_NN1_ (D, C, R, Q);
    input D;
    input C;
    input R;
    output Q;
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    sdffnsn _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .SN(R));
endmodule
