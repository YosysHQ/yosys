module opt_rmdff_test (input C, input D, input E, output reg [16:0] Q);
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove0 (.CLK(C), .D(D), .EN(1'b0), .Q(Q[0]));
initial Q[1] = 1'b1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove1 (.CLK(C), .D(D), .EN(1'b0), .Q(Q[1]));
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove2 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[2]));
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep2 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[2]));
initial Q[3] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(1)) keep3 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[3]));
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove4 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[4]));
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove5 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[5]));
initial Q[6] = 1'b0;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(0)) keep6 (.CLK(C), .D(D), .EN(E), .Q(Q[6]));

\$_DFFE_PP_ remove7 (.C(C), .D(D), .E(1'b0), .Q(Q[7]));
initial Q[8] = 1'b1;
\$_DFFE_PP_ remove8 (.C(C), .D(D), .E(1'b0), .Q(Q[8]));
\$_DFFE_PP_ remove9 (.C(C), .D(D), .E(1'bx), .Q(Q[9]));
\$_DFFE_PP_ keep10 (.C(C), .D(D), .E(1'b1), .Q(Q[10]));
initial Q[11] = 1'b0;
\$_DFFE_PP_ keep11 (.C(C), .D(D), .E(1'b1), .Q(Q[11]));

\$_DFFE_NN_ remove12 (.C(C), .D(D), .E(1'b1), .Q(Q[12]));
initial Q[13] = 1'b1;
\$_DFFE_NN_ remove13 (.C(C), .D(D), .E(1'b1), .Q(Q[13]));
\$_DFFE_NN_ remove14 (.C(C), .D(D), .E(1'bx), .Q(Q[14]));
\$_DFFE_NN_ keep15 (.C(C), .D(D), .E(1'b0), .Q(Q[15]));
initial Q[16] = 1'b0;
\$_DFFE_NN_ keep16 (.C(C), .D(D), .E(1'b0), .Q(Q[16]));

endmodule
