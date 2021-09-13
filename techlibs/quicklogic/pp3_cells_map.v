module \$_MUX8_ (
  A, B, C, D, E, F, G, H, S, T, U, Y
);
  input A, B, C, D, E, F, G, H, S, T, U;
  output Y;
  mux8x0 _TECHMAP_REPLACE_ (
    .A(A),
    .B(B),
    .C(C),
    .D(D),
    .E(E),
    .F(F),
    .G(G),
    .H(H),
    .S0(S),
    .S1(T),
    .S2(U),
    .Q(Y)
  );
endmodule

module \$_MUX4_ (
  A, B, C, D, S, T, U, Y
);
  input A, B, C, D, S, T, U;
  output Y;
  mux4x0 _TECHMAP_REPLACE_ (
    .A(A),
    .B(B),
    .C(C),
    .D(D),
    .S0(S),
    .S1(T),
    .Q(Y)
  );
endmodule
