module  \$_DFF_P_ (input D, C, output Q); LUTFF _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C)); endmodule
//module  \$_DFF_N_ (input D, C, output Q); SB_DFFN _TECHMAP_REPLACE_ (.D(D), .O(Q), .C(C)); endmodule
//module  \$_DFF_P_ (input D, C, output Q); SB_DFF  _TECHMAP_REPLACE_ (.D(D), .O(Q), .C(C)); endmodule

//module  \$_DFFE_NP_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .O(Q), .C(C), .E(E)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); LUTFF_E  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E)); endmodule

//module  \$_DFF_NP0_ (input D, C, R, output Q); SB_DFFNR _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .R(R)); endmodule
//module  \$_DFF_NP1_ (input D, C, R, output Q); SB_DFFNS _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .S(R)); endmodule
//module  \$_DFF_PP0_ (input D, C, R, output Q); LUTFF_R  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .R(R)); endmodule
//module  \$_DFF_PP1_ (input D, C, R, output Q); LUTFF_S  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .S(R)); endmodule

//module  \$_DFFE_NP0P_ (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .R(R)); endmodule
//module  \$_DFFE_NP1P_ (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .S(R)); endmodule
//module  \$_DFFE_PP0P_ (input D, C, E, R, output Q); LUTFF_ER  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .R(R)); endmodule
//module  \$_DFFE_PP1P_ (input D, C, E, R, output Q); LUTFF_ES  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .S(R)); endmodule

//module  \$_SDFF_NP0_ (input D, C, R, output Q); SB_DFFNSR _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .R(R)); endmodule
//module  \$_SDFF_NP1_ (input D, C, R, output Q); SB_DFFNSS _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .S(R)); endmodule
module  \$_SDFF_PP0_ (input D, C, R, output Q); LUTFF_SR  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .R(R)); endmodule
module  \$_SDFF_PP1_ (input D, C, R, output Q); LUTFF_SS  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .S(R)); endmodule

//module  \$_SDFFCE_NP0P_ (input D, C, E, R, output Q); SB_DFFNESR _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .R(R)); endmodule
//module  \$_SDFFCE_NP1P_ (input D, C, E, R, output Q); SB_DFFNESS _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .S(R)); endmodule
module  \$_SDFFCE_PP0P_ (input D, C, E, R, output Q); LUTFF_ESR  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .R(R)); endmodule
module  \$_SDFFCE_PP1P_ (input D, C, E, R, output Q); LUTFF_ESS  _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C), .E(E), .S(R)); endmodule