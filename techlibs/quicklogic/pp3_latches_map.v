module \$_DLATCH_P_ (E, D, Q);
    input E;
    input D;
    output reg Q;
    LUT3 #(.INIT(8'b11100010)) latchimpl (.O(Q), .I2(D), .I1(E), .I0(Q));
endmodule

module \$_DLATCH_N_ (E, D, Q);
    input E;
    input D;
    output reg Q;
    LUT3 #(.INIT(8'b10111000)) latchimpl (.O(Q), .I2(D), .I1(E), .I0(Q));
endmodule

module \$_DLATCHSR_NNN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b101011001111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NNP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b101011001111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NPN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111010110)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_NPP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111010110)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PNN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b110010101111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PNP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b110010101111111)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PPN_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b111111111100101)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b1000)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule

module \$_DLATCHSR_PPP_ (E, S, R, D, Q);
    input E;
    input S;
    input R;
    input D;
    output Q;
    wire SEDQ;
    LUT4 #(.INIT(16'b11111111110010)) sedqlut (.O(SEDQ), .I3(S), .I2(E), .I1(D), .I0(Q));
    LUT2 #(.INIT(4'b0010)) sedr (.O(Q), .I1(R), .I0(SEDQ));
endmodule
