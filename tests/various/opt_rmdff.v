module opt_rmdff_test (input C, input D, input E, output reg [29:0] Q);
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove0 (.CLK(C), .D(D), .EN(1'b0), .Q(Q[0])); // EN is never active
initial Q[1] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove1 (.CLK(C), .D(D), .EN(1'b0), .Q(Q[1])); // EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove2 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[2])); // EN is don't care
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep3 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[3])); // EN is always active
initial Q[3] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(1)) keep4 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[4])); // EN is always active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove5 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[5])); // EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove6 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[6])); // EN is don't care
initial Q[6] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(0)) keep7 (.CLK(C), .D(D), .EN(E), .Q(Q[7])); // EN is non constant

\$_DFFE_PP_ remove8 (.C(C), .D(D), .E(1'b0), .Q(Q[8])); // EN is never active
initial Q[9] = 1'b1;
\$_DFFE_PP_ remove9 (.C(C), .D(D), .E(1'b0), .Q(Q[9])); // EN is never active
\$_DFFE_PP_ remove10 (.C(C), .D(D), .E(1'bx), .Q(Q[10])); // EN is don't care
\$_DFFE_PP_ keep11 (.C(C), .D(D), .E(1'b1), .Q(Q[11])); // EN is always active
initial Q[12] = 1'b0;
\$_DFFE_PP_ keep12 (.C(C), .D(D), .E(1'b1), .Q(Q[12])); // EN is always active

\$_DFFE_NN_ remove13 (.C(C), .D(D), .E(1'b1), .Q(Q[13])); // EN is never active
initial Q[14] = 1'b1;
\$_DFFE_NN_ remove14 (.C(C), .D(D), .E(1'b1), .Q(Q[14])); // EN is never active
\$_DFFE_NN_ remove15 (.C(C), .D(D), .E(1'bx), .Q(Q[15])); // EN is don't care
\$_DFFE_NN_ keep16 (.C(C), .D(D), .E(1'b0), .Q(Q[16])); // EN is always active
initial Q[17] = 1'b0;
\$_DFFE_NN_ keep17 (.C(C), .D(D), .E(1'b0), .Q(Q[17])); // EN is always active

\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove18 (.CLK(1'b0), .D(D), .EN(E), .Q(Q[18])); // CLK is constant
initial Q[19] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove19 (.CLK(1'b1), .D(D), .EN(E), .Q(Q[19])); // CLK is constant
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove20 (.CLK(C), .D(1'bx), .EN(E), .Q(Q[20])); // D is undriven, Q has no initial value
initial Q[21] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep21 (.CLK(C), .D(1'bx), .EN(E), .Q(Q[21])); // D is undriven, Q has initial value
//\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(1)) remove22 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q[22])); // D is constant, no initial Q value, EN is always active
//                                                                                                           // (TODO, Q starts with 1'bx and becomes 1'b0)
initial Q[23] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) noenable23 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q[23])); // D is constant, initial Q value same as D, EN is always active
initial Q[24] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) keep24 (.CLK(C), .D(1'b0), .EN(1'b0), .Q(Q[24])); // D is constant, initial Q value NOT same as D, EN is always active
initial Q[25] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove25 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q[25])); // D is constant, EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove26 (.CLK(C), .D(Q[26]), .EN(1'b1), .Q(Q[26])); // D is Q, EN is always active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove27 (.CLK(C), .D(Q[27]), .EN(1'b1), .Q(Q[27])); // D is Q, EN is never active, but no initial value
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove28 (.CLK(C), .D(Q[28]), .EN(E), .Q(Q[28])); // EN is nonconst, but no initial value
initial Q[29] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep29 (.CLK(C), .D(Q[29]), .EN(1'b1), .Q(Q[29])); // EN is always active, but with initial value

endmodule
