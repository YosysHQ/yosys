module \$_DFF_ (D, CQZ, QCK, QEN, QRT, QST);
    input D;
    input QCK;
    input QEN;
    input QRT;
    input QST;
    output CQZ;
    ff _TECHMAP_REPLACE_ (.CQZ(CQZ), .D(D), .QCK(QCK), .QEN(QEN), .QRT(QRT), .QST(QST));
endmodule

module \$_DFF_N_ (D, Q, C);
    input D;
    input C;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(1'b0), .QST(1'b0));
endmodule

module \$_DFF_P_ (D, Q, C);
    input D;
    input C;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(1'b0), .QST(1'b0));
endmodule

module \$_DFF_NN0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(!R), .QST(1'b0));
endmodule

module \$_DFF_NN1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(1'b0), .QST(!R));
endmodule

module \$_DFF_NP0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(R), .QST(1'b0));
endmodule

module \$_DFF_NP1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(1'b0), .QST(R));
endmodule

module \$_DFF_PN0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(!R), .QST(1'b0));
endmodule

module \$_DFF_PN1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(1'b0), .QST(!R));
endmodule

module \$_DFF_PP0_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(R), .QST(1'b0));
endmodule

module \$_DFF_PP1_ (D, Q, C, R);
    input D;
    input C;
    input R;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(1'b0), .QST(R));
endmodule

module \$_DFFSR_NPP_ (D, Q, C, R, S);
    input D;
    input C;
    input R;
    input S;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(1'b1), .QRT(R), .QST(S));
endmodule

module \$_DFFSR_PPP_ (D, Q, C, R, S);
    input D;
    input C;
    input R;
    input S;
    output Q;
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(1'b1), .QRT(R), .QST(S));
endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(!E), .QRT(1'b0), .QST(1'b0));
 endmodule

module  \$_DFFE_PN_ (input D, C, E, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(!E), .QRT(1'b0), .QST(1'b0));
endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(E), .QRT(1'b0), .QST(1'b0));
endmodule

module  \$_DFFE_PP_ (input D, C, E, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(E), .QRT(1'b0), .QST(1'b0));
endmodule

module  \$__DFFE_NN0 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(E), .QRT(!R), .QST(1'b0));
endmodule

module  \$__DFFE_NN1 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(E), .QRT(1'b0), .QST(!R));
endmodule

module  \$__DFFE_PN0 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(E), .QRT(!R), .QST(1'b0));
endmodule

module  \$__DFFE_PN1 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(E), .QRT(1'b0), .QST(!R));
endmodule

module  \$__DFFE_NP0 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(E), .QRT(R), .QST(1'b0));
endmodule

module  \$__DFFE_NP1 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C), .QEN(E), .QRT(1'b0), .QST(R));
endmodule

module  \$__DFFE_PP0 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(E), .QRT(R), .QST(1'b0));
endmodule

module  \$__DFFE_PP1 (input D, C, E, R, output Q); 
    ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C), .QEN(E), .QRT(1'b0), .QST(R));
endmodule