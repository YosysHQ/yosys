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

module NX_CDC_U_2DFF(CK1, CK2, ADRSTI, ADRSTO, BDRSTI, BDRSTO, BI, AO, BO, AI);
    input ADRSTI;
    output ADRSTO;
    input [5:0] AI;
    output [5:0] AO;
    input BDRSTI;
    output BDRSTO;
    input [5:0] BI;
    output [5:0] BO;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter use_adest_arst = 1'b0;
    parameter use_bdest_arst = 1'b0;

  NX_CDC_U #(
    .mode(0), // -- 0: 2DFF
    .ck0_edge(ck0_edge),
    .ck1_edge(ck1_edge),
    .ack_sel(ack_sel),
    .bck_sel(bck_sel),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(1'b0),
    .use_adest_arst(use_adest_arst),
    .use_bsrc_arst(1'b0),
    .use_bdest_arst(use_bdest_arst),
    .use_csrc_arst(1'b0),
    .use_cdest_arst(1'b0),
    .use_dsrc_arst(1'b0),
    .use_ddest_arst(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
    .ASRSTI(1'b0),
    .ADRSTI(ADRSTI),
    .ADRSTO(ADRSTO),
    .AI1(AI[0]),
    .AI2(AI[1]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AO1(AO[0]),
    .AO2(AO[1]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .BSRSTI(1'b0),
    .BDRSTI(BDRSTI),
    .BDRSTO(BDRSTO),
    .BI1(BI[0]),
    .BI2(BI[1]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BO1(BO[0]),
    .BO2(BO[1]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .CSRSTI(1'b0),
    .CDRSTI(1'b0),
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DSRSTI(1'b0),
    .DDRSTI(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0),
  );
endmodule

module NX_CDC_U_3DFF(CK1, CK2, ASRSTI, ADRSTI, ASRSTO, ADRSTO, BSRSTI, BDRSTI, BSRSTO, BDRSTO, BI, AO, BO, AI);
    input ADRSTI;
    output ADRSTO;
    input [5:0] AI;
    output [5:0] AO;
    input ASRSTI;
    output ASRSTO;
    input BDRSTI;
    output BDRSTO;
    input [5:0] BI;
    output [5:0] BO;
    input BSRSTI;
    output BSRSTO;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter use_adest_arst = 1'b0;
    parameter use_asrc_arst = 1'b0;
    parameter use_bdest_arst = 1'b0;
    parameter use_bsrc_arst = 1'b0;

  NX_CDC_U #(
    .mode(1), // -- 1: 3DFF
    .ck0_edge(ck0_edge),
    .ck1_edge(ck1_edge),
    .ack_sel(ack_sel),
    .bck_sel(bck_sel),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(use_asrc_arst),
    .use_adest_arst(use_adest_arst),
    .use_bsrc_arst(use_bsrc_arst),
    .use_bdest_arst(use_bdest_arst),
    .use_csrc_arst(1'b0),
    .use_cdest_arst(1'b0),
    .use_dsrc_arst(1'b0),
    .use_ddest_arst(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
    .ASRSTI(ASRSTI),
    .ADRSTI(ADRSTI),
    .ASRSTO(ASRSTO),
    .ADRSTO(ADRSTO),
    .AI1(AI[0]),
    .AI2(AI[1]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AO1(AO[0]),
    .AO2(AO[1]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .BSRSTI(BSRSTI),
    .BDRSTI(BDRSTI),
    .BSRSTO(BSRSTO),
    .BDRSTO(BDRSTO),
    .BI1(BI[0]),
    .BI2(BI[1]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BO1(BO[0]),
    .BO2(BO[1]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .CSRSTI(1'b0),
    .CDRSTI(1'b0),
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DSRSTI(1'b0),
    .DDRSTI(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0),
  );
endmodule

module NX_CDC_U_FULL(CK1, CK2, ASRSTI, ADRSTI, ASRSTO, ADRSTO, BSRSTI, BDRSTI, BSRSTO, BDRSTO, BI, AO, BO, AI);
    input ADRSTI;
    output ADRSTO;
    input [5:0] AI;
    output [5:0] AO;
    input ASRSTI;
    output ASRSTO;
    input BDRSTI;
    output BDRSTO;
    input [5:0] BI;
    output [5:0] BO;
    input BSRSTI;
    output BSRSTO;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter use_adest_arst = 1'b0;
    parameter use_asrc_arst = 1'b0;
    parameter use_bdest_arst = 1'b0;
    parameter use_bsrc_arst = 1'b0;

  NX_CDC_U #(
    .mode(2), // -- 2: bin2gray + 3DFF + gray2bin
    .ck0_edge(ck0_edge),
    .ck1_edge(ck1_edge),
    .ack_sel(ack_sel),
    .bck_sel(bck_sel),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(use_asrc_arst),
    .use_adest_arst(use_adest_arst),
    .use_bsrc_arst(use_bsrc_arst),
    .use_bdest_arst(use_bdest_arst),
    .use_csrc_arst(1'b0),
    .use_cdest_arst(1'b0),
    .use_dsrc_arst(1'b0),
    .use_ddest_arst(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
    .ASRSTI(ASRSTI),
    .ADRSTI(ADRSTI),
    .ASRSTO(ASRSTO),
    .ADRSTO(ADRSTO),
    .AI1(AI[0]),
    .AI2(AI[1]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AO1(AO[0]),
    .AO2(AO[1]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .BSRSTI(BSRSTI),
    .BDRSTI(BDRSTI),
    .BSRSTO(BSRSTO),
    .BDRSTO(BDRSTO),
    .BI1(BI[0]),
    .BI2(BI[1]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BO1(BO[0]),
    .BO2(BO[1]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .CSRSTI(1'b0),
    .CDRSTI(1'b0),
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DSRSTI(1'b0),
    .DDRSTI(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0),
  );
endmodule

module NX_CDC_U_BIN2GRAY(BI, AO, BO, AI);
    input [5:0] AI;
    output [5:0] AO;
    input [5:0] BI;
    output [5:0] BO;

  NX_CDC_U #(
    .mode(3), // -- 3: bin2gray
    .ck0_edge(1'b0),
    .ck1_edge(1'b0),
    .ack_sel(1'b0),
    .bck_sel(1'b0),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(1'b0),
    .use_adest_arst(1'b0),
    .use_bsrc_arst(1'b0),
    .use_bdest_arst(1'b0),
    .use_csrc_arst(1'b0),
    .use_cdest_arst(1'b0),
    .use_dsrc_arst(1'b0),
    .use_ddest_arst(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(1'b0),
    .CK2(1'b0),
    .ASRSTI(1'b0),
    .ADRSTI(1'b0),
    .AI1(AI[0]),
    .AI2(AI[1]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AO1(AO[0]),
    .AO2(AO[1]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .BSRSTI(1'b0),
    .BDRSTI(1'b0),
    .BI1(BI[0]),
    .BI2(BI[1]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BO1(BO[0]),
    .BO2(BO[1]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .CSRSTI(1'b0),
    .CDRSTI(1'b0),
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DSRSTI(1'b0),
    .DDRSTI(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0),
  );
endmodule

module NX_CDC_U_GRAY2BIN(BI, AO, BO, AI);
    input [5:0] AI;
    output [5:0] AO;
    input [5:0] BI;
    output [5:0] BO;

  NX_CDC_U #(
    .mode(4), // -- 4: gray2bin
    .ck0_edge(1'b0),
    .ck1_edge(1'b0),
    .ack_sel(1'b0),
    .bck_sel(1'b0),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(1'b0),
    .use_adest_arst(1'b0),
    .use_bsrc_arst(1'b0),
    .use_bdest_arst(1'b0),
    .use_csrc_arst(1'b0),
    .use_cdest_arst(1'b0),
    .use_dsrc_arst(1'b0),
    .use_ddest_arst(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(1'b0),
    .CK2(1'b0),
    .ASRSTI(1'b0),
    .ADRSTI(1'b0),
    .AI1(AI[0]),
    .AI2(AI[1]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AO1(AO[0]),
    .AO2(AO[1]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .BSRSTI(1'b0),
    .BDRSTI(1'b0),
    .BI1(BI[0]),
    .BI2(BI[1]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BO1(BO[0]),
    .BO2(BO[1]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .CSRSTI(1'b0),
    .CDRSTI(1'b0),
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DSRSTI(1'b0),
    .DDRSTI(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0),
  );
endmodule

