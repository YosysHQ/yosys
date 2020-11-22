module \$_DFF_N_ (D, Q, C);
    input D;
    input C;
    output Q;
    openfpga_ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(!C));
endmodule

module \$_DFF_P_ (D, Q, C);
    input D;
    input C;
    output Q;
    openfpga_ff _TECHMAP_REPLACE_ (.CQZ(Q), .D(D), .QCK(C));
endmodule


