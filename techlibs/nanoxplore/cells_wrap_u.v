module NX_CKS_U(CKI, CMD, CKO);
    input CKI;
    output CKO;
    input CMD;

NX_GCK_U #(
    .inv_in(1'b0),
    .inv_out(1'b0),
    .std_mode("CKS")
) _TECHMAP_REPLACE_ (
    .CMD(CMD),
    .SI1(CKI),
    .SI2(1'b0),
    .SO(CKO)
);
endmodule

module NX_CMUX_U(CKI0, CKI1, SEL, CKO);
    input CKI0;
    input CKI1;
    output CKO;
    input SEL;

NX_GCK_U #(
    .inv_in(1'b0),
    .inv_out(1'b0),
    .std_mode("MUX")
) _TECHMAP_REPLACE_ (
    .CMD(SEL),
    .SI1(CKI0),
    .SI2(CKI1),
    .SO(CKO)
);
endmodule
