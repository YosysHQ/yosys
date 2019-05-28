module opt_rmdff_test (input C, input D, input E, output [29:0] Q);
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove0 (.CLK(C), .D(D), .EN(1'b0), .Q(Q[0])); // EN is never active
(* init = "1'b1" *) wire Q1; assign Q[1] = Q1;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove1 (.CLK(C), .D(D), .EN(1'b0), .Q(Q1)); // EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove2 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[2])); // EN is don't care
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep3 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[3])); // EN is always active
(* init = "1'b0" *) wire Q4; assign Q[4] = Q4;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(1)) keep4 (.CLK(C), .D(D), .EN(1'b1), .Q(Q4)); // EN is always active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove5 (.CLK(C), .D(D), .EN(1'b1), .Q(Q[5])); // EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove6 (.CLK(C), .D(D), .EN(1'bx), .Q(Q[6])); // EN is don't care
(* init = "1'b0" *) wire Q7; assign Q[7] = Q7;
\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(0)) keep7 (.CLK(C), .D(D), .EN(E), .Q(Q7)); // EN is non constant

\$_DFFE_PP_ remove8 (.C(C), .D(D), .E(1'b0), .Q(Q[8])); // EN is never active
(* init = "1'b1" *) wire Q9; assign Q[9] = Q9;
\$_DFFE_PP_ remove9 (.C(C), .D(D), .E(1'b0), .Q(Q9)); // EN is never active
\$_DFFE_PP_ remove10 (.C(C), .D(D), .E(1'bx), .Q(Q[10])); // EN is don't care
\$_DFFE_PP_ keep11 (.C(C), .D(D), .E(1'b1), .Q(Q[11])); // EN is always active
(* init = "1'b0" *) wire Q12; assign Q[12] = Q12;
\$_DFFE_PP_ keep12 (.C(C), .D(D), .E(1'b1), .Q(Q12)); // EN is always active

\$_DFFE_NN_ remove13 (.C(C), .D(D), .E(1'b1), .Q(Q[13])); // EN is never active
(* init = "1'b1" *) wire Q14; assign Q[14] = Q14;
\$_DFFE_NN_ remove14 (.C(C), .D(D), .E(1'b1), .Q(Q14)); // EN is never active
\$_DFFE_NN_ remove15 (.C(C), .D(D), .E(1'bx), .Q(Q[15])); // EN is don't care
\$_DFFE_NN_ keep16 (.C(C), .D(D), .E(1'b0), .Q(Q[16])); // EN is always active
(* init = "1'b0" *) wire Q17; assign Q[17] = Q17;
\$_DFFE_NN_ keep17 (.C(C), .D(D), .E(1'b0), .Q(Q17)); // EN is always active

\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove18 (.CLK(1'b0), .D(D), .EN(E), .Q(Q[18])); // CLK is constant
(* init = "1'b1" *) wire Q19; assign Q[19] = Q19;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove19 (.CLK(1'b1), .D(D), .EN(E), .Q(Q19)); // CLK is constant
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove20 (.CLK(C), .D(1'bx), .EN(E), .Q(Q[20])); // D is undriven, Q has no initial value
(* init = "1'b0" *) wire Q21; assign Q[21] = Q21;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep21 (.CLK(C), .D(1'bx), .EN(E), .Q(Q21)); // D is undriven, Q has initial value
//\$dffe #(.WIDTH(1), .CLK_POLARITY(0), .EN_POLARITY(1)) remove22 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q[22])); // D is constant, no initial Q value, EN is always active
//                                                                                                           // (TODO, Q starts with 1'bx and becomes 1'b0)
(* init = "1'b0" *) wire Q23; assign Q[23] = Q23;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) noenable23 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q23)); // D is constant, initial Q value same as D, EN is always active
(* init = "1'b1" *) wire Q24; assign Q[24] = Q24;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) keep24 (.CLK(C), .D(1'b0), .EN(1'b0), .Q(Q24)); // D is constant, initial Q value NOT same as D, EN is always active
(* init = "1'b1" *) wire Q25; assign Q[25] = Q25;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove25 (.CLK(C), .D(1'b0), .EN(1'b1), .Q(Q25)); // D is constant, EN is never active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) remove26 (.CLK(C), .D(Q[26]), .EN(1'b1), .Q(Q[26])); // D is Q, EN is always active
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove27 (.CLK(C), .D(Q[27]), .EN(1'b1), .Q(Q[27])); // D is Q, EN is never active, but no initial value
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(0)) remove28 (.CLK(C), .D(Q[28]), .EN(E), .Q(Q[28])); // EN is nonconst, but no initial value
(* init = "1'b1" *) wire Q29; assign Q[29] = Q29;
\$dffe #(.WIDTH(1), .CLK_POLARITY(1), .EN_POLARITY(1)) keep29 (.CLK(C), .D(Q[29]), .EN(1'b1), .Q(Q29)); // EN is always active, but with initial value

endmodule
