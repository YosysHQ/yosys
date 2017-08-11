module __FULL_ADDER_ (input A, input B, input Cin, output Y, output Cout);
    __XOR3_ xor3 (
        .A(A),
        .B(B),
        .C(Cin),
        .Y(Y),
    );

    __MAJ_ maj (
        .A(A),
        .B(B),
        .C(Cin),
        .Y(Cout),
    );
endmodule

module __HALF_ADDER_ (input A, input B, output Y, output Cout);
    $_XOR_ xorgate (
        .A(A),
        .B(B),
        .Y(Y),
    );

    $_AND_ andgate (
        .A(A),
        .B(B),
        .Y(Cout),
    );
endmodule

module __FULL_SUBTRACTOR_ (input A, input B, input Bin, output Y, output Bout);
    wire nA;

    $_NOT_ notgate (
        .A(A),
        .Y(nA),
    );

    __XOR3_ xor3 (
        .A(A),
        .B(B),
        .C(Bin),
        .Y(Y),
    );

    __MAJ_ maj (
        .A(nA),
        .B(B),
        .C(Bin),
        .Y(Bout),
    );
endmodule

module __HALF_SUBTRACTOR_ (input A, input B, output Y, output Bout);
    wire nA;

    $_NOT_ notgate (
        .A(A),
        .Y(nA),
    );

    $_XOR_ xorgate (
        .A(A),
        .B(B),
        .Y(Y),
    );

    $_AND_ andgate (
        .A(nA),
        .B(B),
        .Y(Bout),
    );
endmodule
