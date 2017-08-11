module __XOR3_ (input A, input B, input C, output Y);
    wire intermed;

    $_XOR_ xorgate1(
        .A(A),
        .B(B),
        .Y(intermed),
    );

    $_XOR_ xorgate2(
        .A(intermed),
        .B(C),
        .Y(Y),
    );
endmodule

module __MAJ_ (input A, input B, input C, output Y);
    wire intermed1;
    wire intermed2;
    wire intermed3;

    wire intermed4;

    $_AND_ andgate1(
        .A(A),
        .B(B),
        .Y(intermed1),
    );

    $_AND_ andgate2(
        .A(A),
        .B(C),
        .Y(intermed2),
    );

    $_AND_ andgate3(
        .A(B),
        .B(C),
        .Y(intermed3),
    );

    $_OR_ orgate1(
        .A(intermed1),
        .B(intermed2),
        .Y(intermed4),
    );

    $_OR_ orgate2(
        .A(intermed4),
        .B(intermed3),
        .Y(Y),
    );
endmodule
