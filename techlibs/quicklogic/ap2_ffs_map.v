module  \$_DFF_N_ (input D, C, output Q); 
    dff _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C)); 
endmodule

module  \$_DFF_P_ (input D, C, output Q);
    dff  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C)); 
endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); 
    dffe _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(!E)); 
endmodule

module  \$_DFFE_PN_ (input D, C, E, output Q); 
    dffe  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(!E)); 
endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); 
    dffe _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(E)); 
endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); 
    dffe  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(E)); 
endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); 
    dffc _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .CLR(!R)); 
endmodule

module  \$_DFF_NN1_ (input D, C, R, output Q); 
    dffp _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .PRE(!R)); 
endmodule

module  \$_DFF_PN0_ (input D, C, R, output Q); 
    dffc  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLR(!R)); 
endmodule

module  \$_DFF_PN1_ (input D, C, R, output Q); 
    dffp  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRE(!R)); 
endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); 
    dffc _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .CLR(R)); 
endmodule

module  \$_DFF_NP1_ (input D, C, R, output Q); 
    dffp _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .PRE(R)); 
endmodule

module  \$_DFF_PP0_ (input D, C, R, output Q); 
    dffc  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLR(R)); 
endmodule

module  \$_DFF_PP1_ (input D, C, R, output Q); 
    dffp  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRE(R)); 
endmodule

module  \$__DFFE_NN0 (input D, C, E, R, output Q); 
    dffsec _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(E), .CLR(!R)); 
endmodule

module  \$__DFFE_NN1 (input D, C, E, R, output Q); 
    dffsep _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(E), .P(!R)); 
endmodule

module  \$__DFFE_PN0 (input D, C, E, R, output Q); 
    dffsec  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(E), .CLR(!R)); 
endmodule

module  \$__DFFE_PN1 (input D, C, E, R, output Q); 
    dffsep  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(E), .P(!R));
endmodule

module  \$__DFFE_NP0 (input D, C, E, R, output Q); 
    dffsec _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(E), .CLR(R)); 
endmodule

module  \$__DFFE_NP1 (input D, C, E, R, output Q); 
    dffsep _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(!C), .EN(E), .P(R)); 
endmodule

module  \$__DFFE_PP0 (input D, C, E, R, output Q); 
    dffsec  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(E), .CLR(R)); 
endmodule

module  \$__DFFE_PP1 (input D, C, E, R, output Q); 
    dffsep  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .EN(E), .P(R)); 
endmodule

module \$_DFFSR_NPP_ (input D, C, R, S, output Q);
    dffpc _TECHMAP_REPLACE_ (.Q(Q), .D(D), .CLK(!C), .CLR(R), .PRE(S));
endmodule

module \$_DFFSR_PPP_ (input D, C, R, S, output Q);
    dffpc _TECHMAP_REPLACE_ (.Q(Q), .D(D), .CLK(C), .CLR(R), .PRE(S));
endmodule