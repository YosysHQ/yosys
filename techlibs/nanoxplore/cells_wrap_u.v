
module NX_ODDFR_U(CK,R,I1,I2,L,O);
    input CK;
    input R;
    input I1;
    input I2;
    input L;
    output O;

    parameter location = "";
    parameter path = 0;
    parameter dff_type = 1'b0;
    parameter dff_sync = 1'b0;
    parameter dff_load = 1'b0;

  NX_DDFR_U #(
      .location(location),
      .path(path),
      .dff_type(dff_type),
      .dff_sync(dff_sync),
      .dff_load(dff_load)
  ) _TECHMAP_REPLACE_ (
      .CK(CK),
      .CKF(CK),
      .R(R),
      .I(I1),
      .I2(I2),
      .L(L),
      .O(O),
      .O2()
  );
endmodule

module NX_IDDFR_U(CK,R,I,L,O1,O2);
    input CK;
    input R;
    input I;
    input L;
    output O1;
    output O2;

    parameter location = "";
    parameter dff_type = 1'b0;
    parameter dff_sync = 1'b0;
    parameter dff_load = 1'b0;

  NX_DDFR_U #(
      .location(location),
      .path(1),
      .dff_type(dff_type),
      .dff_sync(dff_sync),
      .dff_load(dff_load)
  ) _TECHMAP_REPLACE_ (
      .CK(CK),
      .CKF(CK),
      .R(R),
      .I(I),
      .I2(1'b0),
      .L(L),
      .O(O1),
      .O2(O2)
  );
endmodule

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
      .SI2(),
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

module NX_XCDC_U(CK1, CK2, ASRSTI, ADRSTI, ASRSTO, ADRSTO, BSRSTI, BDRSTI, BSRSTO, BDRSTO, CSRSTI, CDRSTI, CSRSTO, CDRSTO, DSRSTI, DDRSTI, DSRSTO, DDRSTO, BI, CI, CO
, AO, BO, AI, DI, DO);
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
    input CDRSTI;
    output CDRSTO;
    input [5:0] CI;
    input CK1;
    input CK2;
    output [5:0] CO;
    input CSRSTI;
    output CSRSTO;
    input DDRSTI;
    output DDRSTO;
    input [5:0] DI;
    output [5:0] DO;
    input DSRSTI;
    output DSRSTO;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter cck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter dck_sel = 1'b0;
    parameter link_BA = 1'b0;
    parameter link_CB = 1'b0;
    parameter link_DC = 1'b0;
    parameter use_adest_arst = 1'b0;
    parameter use_asrc_arst = 1'b0;
    parameter use_bdest_arst = 1'b0;
    parameter use_bsrc_arst = 1'b0;
    parameter use_cdest_arst = 1'b0;
    parameter use_csrc_arst = 1'b0;
    parameter use_ddest_arst = 1'b0;
    parameter use_dsrc_arst = 1'b0;

  NX_CDC_U #(
    .mode(5), // -- 5: XCDC
    .ck0_edge(ck0_edge),
    .ck1_edge(ck1_edge),
    .ack_sel(ack_sel),
    .bck_sel(bck_sel),
    .cck_sel(cck_sel),
    .dck_sel(dck_sel),
    .use_asrc_arst(use_asrc_arst),
    .use_adest_arst(use_adest_arst),
    .use_bsrc_arst(use_bsrc_arst),
    .use_bdest_arst(use_bdest_arst),
    .use_csrc_arst(use_csrc_arst),
    .use_cdest_arst(use_cdest_arst),
    .use_dsrc_arst(use_dsrc_arst),
    .use_ddest_arst(use_ddest_arst),
    .link_BA(link_BA),
    .link_CB(link_CB),
    .link_DC(link_DC),
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
    .CSRSTI(CSRSTI),
    .CDRSTI(CDRSTI),
    .CSRSTO(CSRSTO),
    .CDRSTO(CDRSTO),
    .CI1(CI[0]),
    .CI2(CI[1]),
    .CI3(CI[2]),
    .CI4(CI[3]),
    .CI5(CI[4]),
    .CI6(CI[5]),
    .CO1(CO[0]),
    .CO2(CO[1]),
    .CO3(CO[2]),
    .CO4(CO[3]),
    .CO5(CO[4]),
    .CO6(CO[5]),
    .DSRSTI(DSRSTI),
    .DDRSTI(DDRSTI),
    .DSRSTO(DSRSTO),
    .DDRSTO(DDRSTO),
    .DI1(DI[0]),
    .DI2(DI[1]),
    .DI3(DI[2]),
    .DI4(DI[3]),
    .DI5(DI[4]),
    .DI6(DI[5]),
    .DO1(DO[0]),
    .DO2(DO[1]),
    .DO3(DO[2]),
    .DO4(DO[3]),
    .DO5(DO[4]),
    .DO6(DO[5]),
  );
endmodule

module NX_DSP_U_SPLIT(CK, R, RZ, WE, WEZ, CI, CCI, CO42, CO56, OVF, CCO, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO, CZO);
    input [23:0] A;
    input [17:0] B;
    input [35:0] C;
    input [23:0] CAI;
    output [23:0] CAO;
    input [17:0] CBI;
    output [17:0] CBO;
    input CCI;
    output CCO;
    input CI;
    input CK;
    output CO42;
    output CO56;
    input [55:0] CZI;
    output [55:0] CZO;
    input [17:0] D;
    output OVF;
    input R;
    input RZ;
    input WE;
    input WEZ;
    output [55:0] Z;
    parameter ALU_DYNAMIC_OP = 2'b00;
    parameter ALU_OP = 3'b000;
    parameter ENABLE_PR_A_RST = 1'b0;
    parameter ENABLE_PR_B_RST = 1'b0;
    parameter ENABLE_PR_CCO_RST = 1'b0;
    parameter ENABLE_PR_CI_RST = 1'b0;
    parameter ENABLE_PR_CO_RST = 1'b0;
    parameter ENABLE_PR_CZ_RST = 1'b0;
    parameter ENABLE_PR_C_RST = 1'b0;
    parameter ENABLE_PR_D_RST = 1'b0;
    parameter ENABLE_PR_MULT_RST = 1'b0;
    parameter ENABLE_PR_OV_RST = 1'b0;
    parameter ENABLE_PR_P_RST = 1'b0;
    parameter ENABLE_PR_X_RST = 1'b0;
    parameter ENABLE_PR_Y_RST = 1'b0;
    parameter ENABLE_PR_Z_RST = 1'b0;
    parameter ENABLE_SATURATION = 1'b0;
    parameter INV_RST = 1'b0;
    parameter INV_RSTZ = 1'b0;
    parameter INV_WE = 1'b0;
    parameter INV_WEZ = 1'b0;
    parameter MUX_A = 1'b0;
    parameter MUX_B = 1'b0;
    parameter MUX_CCI = 1'b0;
    parameter MUX_CCO = 1'b0;
    parameter MUX_CI = 1'b0;
    parameter MUX_CZ = 1'b0;
    parameter MUX_P = 1'b0;
    parameter MUX_X = 3'b000;
    parameter MUX_Y = 1'b0;
    parameter MUX_Z = 1'b0;
    parameter PRE_ADDER_OP = 1'b0;
    parameter PR_A_CASCADE_MUX = 2'b00;
    parameter PR_A_MUX = 2'b00;
    parameter PR_B_CASCADE_MUX = 2'b00;
    parameter PR_B_MUX = 2'b00;
    parameter PR_CCO_MUX = 1'b0;
    parameter PR_CI_MUX = 1'b0;
    parameter PR_CO_MUX = 1'b0;
    parameter PR_CZ_MUX = 1'b0;
    parameter PR_C_MUX = 1'b0;
    parameter PR_D_MUX = 1'b0;
    parameter PR_MULT_MUX = 1'b0;
    parameter PR_OV_MUX = 1'b0;
    parameter PR_P_MUX = 1'b0;
    parameter PR_RSTZ_MUX = 1'b0;
    parameter PR_RST_MUX = 1'b0;
    parameter PR_WEZ_MUX = 1'b0;
    parameter PR_WE_MUX = 1'b0;
    parameter PR_X_MUX = 1'b0;
    parameter PR_Y_MUX = 1'b0;
    parameter PR_Z_MUX = 1'b0;
    parameter SATURATION_RANK = 6'b000000;
    parameter SIGNED_MODE = 1'b0;

    localparam RAW_CONFIG0_GEN = { INV_WE, INV_WEZ, INV_RST, INV_RSTZ, MUX_CCO, ALU_DYNAMIC_OP, SATURATION_RANK,
     ENABLE_SATURATION, MUX_Z, MUX_CCI, MUX_CI, MUX_Y, MUX_CZ, MUX_X, MUX_P,
     MUX_B, MUX_A, PRE_ADDER_OP, SIGNED_MODE };

    localparam RAW_CONFIG1_GEN = { PR_WE_MUX, PR_WEZ_MUX, PR_RST_MUX, PR_RSTZ_MUX, PR_OV_MUX, PR_CO_MUX, PR_CCO_MUX,
    PR_Z_MUX, PR_CZ_MUX, PR_Y_MUX, PR_X_MUX, PR_CI_MUX, PR_MULT_MUX, PR_P_MUX, PR_D_MUX,
    PR_C_MUX, PR_B_CASCADE_MUX, PR_B_MUX, PR_A_CASCADE_MUX, PR_A_MUX };

    localparam RAW_CONFIG2_GEN = { ENABLE_PR_OV_RST, ENABLE_PR_CO_RST, ENABLE_PR_CCO_RST, ENABLE_PR_Z_RST, ENABLE_PR_CZ_RST,
    ENABLE_PR_MULT_RST, ENABLE_PR_Y_RST, ENABLE_PR_X_RST, ENABLE_PR_P_RST, ENABLE_PR_CI_RST,
    ENABLE_PR_D_RST, ENABLE_PR_C_RST, ENABLE_PR_B_RST, ENABLE_PR_A_RST };

    localparam RAW_CONFIG3_GEN = { ALU_OP };

  NX_DSP_U #(
    .std_mode(""),
    .raw_config0(RAW_CONFIG0_GEN),
    .raw_config1(RAW_CONFIG1_GEN),
    .raw_config2(RAW_CONFIG2_GEN),
    .raw_config3(RAW_CONFIG3_GEN)
  ) _TECHMAP_REPLACE_ (
    .A1(A[0]),
    .A2(A[1]),
    .A3(A[2]),
    .A4(A[3]),
    .A5(A[4]),
    .A6(A[5]),
    .A7(A[6]),
    .A8(A[7]),
    .A9(A[8]),
    .A10(A[9]),
    .A11(A[10]),
    .A12(A[11]),
    .A13(A[12]),
    .A14(A[13]),
    .A15(A[14]),
    .A16(A[15]),
    .A17(A[16]),
    .A18(A[17]),
    .A19(A[18]),
    .A20(A[19]),
    .A21(A[20]),
    .A22(A[21]),
    .A23(A[22]),
    .A24(A[23]),

    .B1(B[0]),
    .B2(B[1]),
    .B3(B[2]),
    .B4(B[3]),
    .B5(B[4]),
    .B6(B[5]),
    .B7(B[6]),
    .B8(B[7]),
    .B9(B[8]),
    .B10(B[9]),
    .B11(B[10]),
    .B12(B[11]),
    .B13(B[12]),
    .B14(B[13]),
    .B15(B[14]),
    .B16(B[15]),
    .B17(B[16]),
    .B18(B[17]),

    .C1(C[0]),
    .C2(C[1]),
    .C3(C[2]),
    .C4(C[3]),
    .C5(C[4]),
    .C6(C[5]),
    .C7(C[6]),
    .C8(C[7]),
    .C9(C[8]),
    .C10(C[9]),
    .C11(C[10]),
    .C12(C[11]),
    .C13(C[12]),
    .C14(C[13]),
    .C15(C[14]),
    .C16(C[15]),
    .C17(C[16]),
    .C18(C[17]),
    .C19(C[18]),
    .C20(C[19]),
    .C21(C[20]),
    .C22(C[21]),
    .C23(C[22]),
    .C24(C[23]),
    .C25(C[24]),
    .C26(C[25]),
    .C27(C[26]),
    .C28(C[27]),
    .C29(C[28]),
    .C30(C[29]),
    .C31(C[30]),
    .C32(C[31]),
    .C33(C[32]),
    .C34(C[33]),
    .C35(C[34]),
    .C36(C[35]),

    .CAI1(CAI[0]),
    .CAI2(CAI[1]),
    .CAI3(CAI[2]),
    .CAI4(CAI[3]),
    .CAI5(CAI[4]),
    .CAI6(CAI[5]),
    .CAI7(CAI[6]),
    .CAI8(CAI[7]),
    .CAI9(CAI[8]),
    .CAI10(CAI[9]),
    .CAI11(CAI[10]),
    .CAI12(CAI[11]),
    .CAI13(CAI[12]),
    .CAI14(CAI[13]),
    .CAI15(CAI[14]),
    .CAI16(CAI[15]),
    .CAI17(CAI[16]),
    .CAI18(CAI[17]),
    .CAI19(CAI[18]),
    .CAI20(CAI[19]),
    .CAI21(CAI[20]),
    .CAI22(CAI[21]),
    .CAI23(CAI[22]),
    .CAI24(CAI[23]),

    .CAO1(CAO[0]),
    .CAO2(CAO[1]),
    .CAO3(CAO[2]),
    .CAO4(CAO[3]),
    .CAO5(CAO[4]),
    .CAO6(CAO[5]),
    .CAO7(CAO[6]),
    .CAO8(CAO[7]),
    .CAO9(CAO[8]),
    .CAO10(CAO[9]),
    .CAO11(CAO[10]),
    .CAO12(CAO[11]),
    .CAO13(CAO[12]),
    .CAO14(CAO[13]),
    .CAO15(CAO[14]),
    .CAO16(CAO[15]),
    .CAO17(CAO[16]),
    .CAO18(CAO[17]),
    .CAO19(CAO[18]),
    .CAO20(CAO[19]),
    .CAO21(CAO[20]),
    .CAO22(CAO[21]),
    .CAO23(CAO[22]),
    .CAO24(CAO[23]),

    .CBI1(CBI[0]),
    .CBI2(CBI[1]),
    .CBI3(CBI[2]),
    .CBI4(CBI[3]),
    .CBI5(CBI[4]),
    .CBI6(CBI[5]),
    .CBI7(CBI[6]),
    .CBI8(CBI[7]),
    .CBI9(CBI[8]),
    .CBI10(CBI[9]),
    .CBI11(CBI[10]),
    .CBI12(CBI[11]),
    .CBI13(CBI[12]),
    .CBI14(CBI[13]),
    .CBI15(CBI[14]),
    .CBI16(CBI[15]),
    .CBI17(CBI[16]),
    .CBI18(CBI[17]),

    .CBO1(CBO[0]),
    .CBO2(CBO[1]),
    .CBO3(CBO[2]),
    .CBO4(CBO[3]),
    .CBO5(CBO[4]),
    .CBO6(CBO[5]),
    .CBO7(CBO[6]),
    .CBO8(CBO[7]),
    .CBO9(CBO[8]),
    .CBO10(CBO[9]),
    .CBO11(CBO[10]),
    .CBO12(CBO[11]),
    .CBO13(CBO[12]),
    .CBO14(CBO[13]),
    .CBO15(CBO[14]),
    .CBO16(CBO[15]),
    .CBO17(CBO[16]),
    .CBO18(CBO[17]),

    .CCI(CCI),
    .CCO(CCO),
    .CI(CI),
    .CK(CK),
    .CO43(CO42),
    .CO57(CO56),

    .CZI1(CZI[0]),
    .CZI2(CZI[1]),
    .CZI3(CZI[2]),
    .CZI4(CZI[3]),
    .CZI5(CZI[4]),
    .CZI6(CZI[5]),
    .CZI7(CZI[6]),
    .CZI8(CZI[7]),
    .CZI9(CZI[8]),
    .CZI10(CZI[9]),
    .CZI11(CZI[10]),
    .CZI12(CZI[11]),
    .CZI13(CZI[12]),
    .CZI14(CZI[13]),
    .CZI15(CZI[14]),
    .CZI16(CZI[15]),
    .CZI17(CZI[16]),
    .CZI18(CZI[17]),
    .CZI19(CZI[18]),
    .CZI20(CZI[19]),
    .CZI21(CZI[20]),
    .CZI22(CZI[21]),
    .CZI23(CZI[22]),
    .CZI24(CZI[23]),
    .CZI25(CZI[24]),
    .CZI26(CZI[25]),
    .CZI27(CZI[26]),
    .CZI28(CZI[27]),
    .CZI29(CZI[28]),
    .CZI30(CZI[29]),
    .CZI31(CZI[30]),
    .CZI32(CZI[31]),
    .CZI33(CZI[32]),
    .CZI34(CZI[33]),
    .CZI35(CZI[34]),
    .CZI36(CZI[35]),
    .CZI37(CZI[36]),
    .CZI38(CZI[37]),
    .CZI39(CZI[38]),
    .CZI40(CZI[39]),
    .CZI41(CZI[40]),
    .CZI42(CZI[41]),
    .CZI43(CZI[42]),
    .CZI44(CZI[43]),
    .CZI45(CZI[44]),
    .CZI46(CZI[45]),
    .CZI47(CZI[46]),
    .CZI48(CZI[47]),
    .CZI49(CZI[48]),
    .CZI50(CZI[49]),
    .CZI51(CZI[50]),
    .CZI52(CZI[51]),
    .CZI53(CZI[52]),
    .CZI54(CZI[53]),
    .CZI55(CZI[54]),
    .CZI56(CZI[55]),

    .CZO1(CZO[0]),
    .CZO2(CZO[1]),
    .CZO3(CZO[2]),
    .CZO4(CZO[3]),
    .CZO5(CZO[4]),
    .CZO6(CZO[5]),
    .CZO7(CZO[6]),
    .CZO8(CZO[7]),
    .CZO9(CZO[8]),
    .CZO10(CZO[9]),
    .CZO11(CZO[10]),
    .CZO12(CZO[11]),
    .CZO13(CZO[12]),
    .CZO14(CZO[13]),
    .CZO15(CZO[14]),
    .CZO16(CZO[15]),
    .CZO17(CZO[16]),
    .CZO18(CZO[17]),
    .CZO19(CZO[18]),
    .CZO20(CZO[19]),
    .CZO21(CZO[20]),
    .CZO22(CZO[21]),
    .CZO23(CZO[22]),
    .CZO24(CZO[23]),
    .CZO25(CZO[24]),
    .CZO26(CZO[25]),
    .CZO27(CZO[26]),
    .CZO28(CZO[27]),
    .CZO29(CZO[28]),
    .CZO30(CZO[29]),
    .CZO31(CZO[30]),
    .CZO32(CZO[31]),
    .CZO33(CZO[32]),
    .CZO34(CZO[33]),
    .CZO35(CZO[34]),
    .CZO36(CZO[35]),
    .CZO37(CZO[36]),
    .CZO38(CZO[37]),
    .CZO39(CZO[38]),
    .CZO40(CZO[39]),
    .CZO41(CZO[40]),
    .CZO42(CZO[41]),
    .CZO43(CZO[42]),
    .CZO44(CZO[43]),
    .CZO45(CZO[44]),
    .CZO46(CZO[45]),
    .CZO47(CZO[46]),
    .CZO48(CZO[47]),
    .CZO49(CZO[48]),
    .CZO50(CZO[49]),
    .CZO51(CZO[50]),
    .CZO52(CZO[51]),
    .CZO53(CZO[52]),
    .CZO54(CZO[53]),
    .CZO55(CZO[54]),
    .CZO56(CZO[55]),

    .D1(D[0]),
    .D2(D[1]),
    .D3(D[2]),
    .D4(D[3]),
    .D5(D[4]),
    .D6(D[5]),
    .D7(D[6]),
    .D8(D[7]),
    .D9(D[8]),
    .D10(D[9]),
    .D11(D[10]),
    .D12(D[11]),
    .D13(D[12]),
    .D14(D[13]),
    .D15(D[14]),
    .D16(D[15]),
    .D17(D[16]),
    .D18(D[17]),

    .OVF(OVF),
    .R(R),
    .RZ(RZ),
    .WE(WE),
    .WEZ(WEZ),

    .Z1(Z[0]),
    .Z2(Z[1]),
    .Z3(Z[2]),
    .Z4(Z[3]),
    .Z5(Z[4]),
    .Z6(Z[5]),
    .Z7(Z[6]),
    .Z8(Z[7]),
    .Z9(Z[8]),
    .Z10(Z[9]),
    .Z11(Z[10]),
    .Z12(Z[11]),
    .Z13(Z[12]),
    .Z14(Z[13]),
    .Z15(Z[14]),
    .Z16(Z[15]),
    .Z17(Z[16]),
    .Z18(Z[17]),
    .Z19(Z[18]),
    .Z20(Z[19]),
    .Z21(Z[20]),
    .Z22(Z[21]),
    .Z23(Z[22]),
    .Z24(Z[23]),
    .Z25(Z[24]),
    .Z26(Z[25]),
    .Z27(Z[26]),
    .Z28(Z[27]),
    .Z29(Z[28]),
    .Z30(Z[29]),
    .Z31(Z[30]),
    .Z32(Z[31]),
    .Z33(Z[32]),
    .Z34(Z[33]),
    .Z35(Z[34]),
    .Z36(Z[35]),
    .Z37(Z[36]),
    .Z38(Z[37]),
    .Z39(Z[38]),
    .Z40(Z[39]),
    .Z41(Z[40]),
    .Z42(Z[41]),
    .Z43(Z[42]),
    .Z44(Z[43]),
    .Z45(Z[44]),
    .Z46(Z[45]),
    .Z47(Z[46]),
    .Z48(Z[47]),
    .Z49(Z[48]),
    .Z50(Z[49]),
    .Z51(Z[50]),
    .Z52(Z[51]),
    .Z53(Z[52]),
    .Z54(Z[53]),
    .Z55(Z[54]),
    .Z56(Z[55])
  );
endmodule

module NX_DSP_U_WRAP(CCI, CCO, CI, CK, CO43, CO57, OVF, R, RZ, WE, WEZ, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO
, CZO);
    input [23:0] A;
    input [17:0] B;
    input [35:0] C;
    input [23:0] CAI;
    output [23:0] CAO;
    input [17:0] CBI;
    output [17:0] CBO;
    input CCI;
    output CCO;
    input CI;
    input CK;
    output CO43;
    output CO57;
    input [55:0] CZI;
    output [55:0] CZO;
    input [17:0] D;
    output OVF;
    input R;
    input RZ;
    input WE;
    input WEZ;
    output [55:0] Z;
    parameter raw_config0 = 27'b000000000000000000000000000;
    parameter raw_config1 = 24'b000000000000000000000000;
    parameter raw_config2 = 14'b00000000000000;
    parameter raw_config3 = 3'b000;
    parameter std_mode = "";

  NX_DSP_U #(
    .std_mode(std_mode),
    .raw_config0(raw_config0),
    .raw_config1(raw_config1),
    .raw_config2(raw_config2),
    .raw_config3(raw_config3)
  ) _TECHMAP_REPLACE_ (
    .A1(A[0]),
    .A2(A[1]),
    .A3(A[2]),
    .A4(A[3]),
    .A5(A[4]),
    .A6(A[5]),
    .A7(A[6]),
    .A8(A[7]),
    .A9(A[8]),
    .A10(A[9]),
    .A11(A[10]),
    .A12(A[11]),
    .A13(A[12]),
    .A14(A[13]),
    .A15(A[14]),
    .A16(A[15]),
    .A17(A[16]),
    .A18(A[17]),
    .A19(A[18]),
    .A20(A[19]),
    .A21(A[20]),
    .A22(A[21]),
    .A23(A[22]),
    .A24(A[23]),

    .B1(B[0]),
    .B2(B[1]),
    .B3(B[2]),
    .B4(B[3]),
    .B5(B[4]),
    .B6(B[5]),
    .B7(B[6]),
    .B8(B[7]),
    .B9(B[8]),
    .B10(B[9]),
    .B11(B[10]),
    .B12(B[11]),
    .B13(B[12]),
    .B14(B[13]),
    .B15(B[14]),
    .B16(B[15]),
    .B17(B[16]),
    .B18(B[17]),

    .C1(C[0]),
    .C2(C[1]),
    .C3(C[2]),
    .C4(C[3]),
    .C5(C[4]),
    .C6(C[5]),
    .C7(C[6]),
    .C8(C[7]),
    .C9(C[8]),
    .C10(C[9]),
    .C11(C[10]),
    .C12(C[11]),
    .C13(C[12]),
    .C14(C[13]),
    .C15(C[14]),
    .C16(C[15]),
    .C17(C[16]),
    .C18(C[17]),
    .C19(C[18]),
    .C20(C[19]),
    .C21(C[20]),
    .C22(C[21]),
    .C23(C[22]),
    .C24(C[23]),
    .C25(C[24]),
    .C26(C[25]),
    .C27(C[26]),
    .C28(C[27]),
    .C29(C[28]),
    .C30(C[29]),
    .C31(C[30]),
    .C32(C[31]),
    .C33(C[32]),
    .C34(C[33]),
    .C35(C[34]),
    .C36(C[35]),

    .CAI1(CAI[0]),
    .CAI2(CAI[1]),
    .CAI3(CAI[2]),
    .CAI4(CAI[3]),
    .CAI5(CAI[4]),
    .CAI6(CAI[5]),
    .CAI7(CAI[6]),
    .CAI8(CAI[7]),
    .CAI9(CAI[8]),
    .CAI10(CAI[9]),
    .CAI11(CAI[10]),
    .CAI12(CAI[11]),
    .CAI13(CAI[12]),
    .CAI14(CAI[13]),
    .CAI15(CAI[14]),
    .CAI16(CAI[15]),
    .CAI17(CAI[16]),
    .CAI18(CAI[17]),
    .CAI19(CAI[18]),
    .CAI20(CAI[19]),
    .CAI21(CAI[20]),
    .CAI22(CAI[21]),
    .CAI23(CAI[22]),
    .CAI24(CAI[23]),

    .CAO1(CAO[0]),
    .CAO2(CAO[1]),
    .CAO3(CAO[2]),
    .CAO4(CAO[3]),
    .CAO5(CAO[4]),
    .CAO6(CAO[5]),
    .CAO7(CAO[6]),
    .CAO8(CAO[7]),
    .CAO9(CAO[8]),
    .CAO10(CAO[9]),
    .CAO11(CAO[10]),
    .CAO12(CAO[11]),
    .CAO13(CAO[12]),
    .CAO14(CAO[13]),
    .CAO15(CAO[14]),
    .CAO16(CAO[15]),
    .CAO17(CAO[16]),
    .CAO18(CAO[17]),
    .CAO19(CAO[18]),
    .CAO20(CAO[19]),
    .CAO21(CAO[20]),
    .CAO22(CAO[21]),
    .CAO23(CAO[22]),
    .CAO24(CAO[23]),

    .CBI1(CBI[0]),
    .CBI2(CBI[1]),
    .CBI3(CBI[2]),
    .CBI4(CBI[3]),
    .CBI5(CBI[4]),
    .CBI6(CBI[5]),
    .CBI7(CBI[6]),
    .CBI8(CBI[7]),
    .CBI9(CBI[8]),
    .CBI10(CBI[9]),
    .CBI11(CBI[10]),
    .CBI12(CBI[11]),
    .CBI13(CBI[12]),
    .CBI14(CBI[13]),
    .CBI15(CBI[14]),
    .CBI16(CBI[15]),
    .CBI17(CBI[16]),
    .CBI18(CBI[17]),

    .CBO1(CBO[0]),
    .CBO2(CBO[1]),
    .CBO3(CBO[2]),
    .CBO4(CBO[3]),
    .CBO5(CBO[4]),
    .CBO6(CBO[5]),
    .CBO7(CBO[6]),
    .CBO8(CBO[7]),
    .CBO9(CBO[8]),
    .CBO10(CBO[9]),
    .CBO11(CBO[10]),
    .CBO12(CBO[11]),
    .CBO13(CBO[12]),
    .CBO14(CBO[13]),
    .CBO15(CBO[14]),
    .CBO16(CBO[15]),
    .CBO17(CBO[16]),
    .CBO18(CBO[17]),

    .CCI(CCI),
    .CCO(CCO),
    .CI(CI),
    .CK(CK),
    .CO43(CO43),
    .CO57(CO57),

    .CZI1(CZI[0]),
    .CZI2(CZI[1]),
    .CZI3(CZI[2]),
    .CZI4(CZI[3]),
    .CZI5(CZI[4]),
    .CZI6(CZI[5]),
    .CZI7(CZI[6]),
    .CZI8(CZI[7]),
    .CZI9(CZI[8]),
    .CZI10(CZI[9]),
    .CZI11(CZI[10]),
    .CZI12(CZI[11]),
    .CZI13(CZI[12]),
    .CZI14(CZI[13]),
    .CZI15(CZI[14]),
    .CZI16(CZI[15]),
    .CZI17(CZI[16]),
    .CZI18(CZI[17]),
    .CZI19(CZI[18]),
    .CZI20(CZI[19]),
    .CZI21(CZI[20]),
    .CZI22(CZI[21]),
    .CZI23(CZI[22]),
    .CZI24(CZI[23]),
    .CZI25(CZI[24]),
    .CZI26(CZI[25]),
    .CZI27(CZI[26]),
    .CZI28(CZI[27]),
    .CZI29(CZI[28]),
    .CZI30(CZI[29]),
    .CZI31(CZI[30]),
    .CZI32(CZI[31]),
    .CZI33(CZI[32]),
    .CZI34(CZI[33]),
    .CZI35(CZI[34]),
    .CZI36(CZI[35]),
    .CZI37(CZI[36]),
    .CZI38(CZI[37]),
    .CZI39(CZI[38]),
    .CZI40(CZI[39]),
    .CZI41(CZI[40]),
    .CZI42(CZI[41]),
    .CZI43(CZI[42]),
    .CZI44(CZI[43]),
    .CZI45(CZI[44]),
    .CZI46(CZI[45]),
    .CZI47(CZI[46]),
    .CZI48(CZI[47]),
    .CZI49(CZI[48]),
    .CZI50(CZI[49]),
    .CZI51(CZI[50]),
    .CZI52(CZI[51]),
    .CZI53(CZI[52]),
    .CZI54(CZI[53]),
    .CZI55(CZI[54]),
    .CZI56(CZI[55]),

    .CZO1(CZO[0]),
    .CZO2(CZO[1]),
    .CZO3(CZO[2]),
    .CZO4(CZO[3]),
    .CZO5(CZO[4]),
    .CZO6(CZO[5]),
    .CZO7(CZO[6]),
    .CZO8(CZO[7]),
    .CZO9(CZO[8]),
    .CZO10(CZO[9]),
    .CZO11(CZO[10]),
    .CZO12(CZO[11]),
    .CZO13(CZO[12]),
    .CZO14(CZO[13]),
    .CZO15(CZO[14]),
    .CZO16(CZO[15]),
    .CZO17(CZO[16]),
    .CZO18(CZO[17]),
    .CZO19(CZO[18]),
    .CZO20(CZO[19]),
    .CZO21(CZO[20]),
    .CZO22(CZO[21]),
    .CZO23(CZO[22]),
    .CZO24(CZO[23]),
    .CZO25(CZO[24]),
    .CZO26(CZO[25]),
    .CZO27(CZO[26]),
    .CZO28(CZO[27]),
    .CZO29(CZO[28]),
    .CZO30(CZO[29]),
    .CZO31(CZO[30]),
    .CZO32(CZO[31]),
    .CZO33(CZO[32]),
    .CZO34(CZO[33]),
    .CZO35(CZO[34]),
    .CZO36(CZO[35]),
    .CZO37(CZO[36]),
    .CZO38(CZO[37]),
    .CZO39(CZO[38]),
    .CZO40(CZO[39]),
    .CZO41(CZO[40]),
    .CZO42(CZO[41]),
    .CZO43(CZO[42]),
    .CZO44(CZO[43]),
    .CZO45(CZO[44]),
    .CZO46(CZO[45]),
    .CZO47(CZO[46]),
    .CZO48(CZO[47]),
    .CZO49(CZO[48]),
    .CZO50(CZO[49]),
    .CZO51(CZO[50]),
    .CZO52(CZO[51]),
    .CZO53(CZO[52]),
    .CZO54(CZO[53]),
    .CZO55(CZO[54]),
    .CZO56(CZO[55]),

    .D1(D[0]),
    .D2(D[1]),
    .D3(D[2]),
    .D4(D[3]),
    .D5(D[4]),
    .D6(D[5]),
    .D7(D[6]),
    .D8(D[7]),
    .D9(D[8]),
    .D10(D[9]),
    .D11(D[10]),
    .D12(D[11]),
    .D13(D[12]),
    .D14(D[13]),
    .D15(D[14]),
    .D16(D[15]),
    .D17(D[16]),
    .D18(D[17]),

    .OVF(OVF),
    .R(R),
    .RZ(RZ),
    .WE(WE),
    .WEZ(WEZ),

    .Z1(Z[0]),
    .Z2(Z[1]),
    .Z3(Z[2]),
    .Z4(Z[3]),
    .Z5(Z[4]),
    .Z6(Z[5]),
    .Z7(Z[6]),
    .Z8(Z[7]),
    .Z9(Z[8]),
    .Z10(Z[9]),
    .Z11(Z[10]),
    .Z12(Z[11]),
    .Z13(Z[12]),
    .Z14(Z[13]),
    .Z15(Z[14]),
    .Z16(Z[15]),
    .Z17(Z[16]),
    .Z18(Z[17]),
    .Z19(Z[18]),
    .Z20(Z[19]),
    .Z21(Z[20]),
    .Z22(Z[21]),
    .Z23(Z[22]),
    .Z24(Z[23]),
    .Z25(Z[24]),
    .Z26(Z[25]),
    .Z27(Z[26]),
    .Z28(Z[27]),
    .Z29(Z[28]),
    .Z30(Z[29]),
    .Z31(Z[30]),
    .Z32(Z[31]),
    .Z33(Z[32]),
    .Z34(Z[33]),
    .Z35(Z[34]),
    .Z36(Z[35]),
    .Z37(Z[36]),
    .Z38(Z[37]),
    .Z39(Z[38]),
    .Z40(Z[39]),
    .Z41(Z[40]),
    .Z42(Z[41]),
    .Z43(Z[42]),
    .Z44(Z[43]),
    .Z45(Z[44]),
    .Z46(Z[45]),
    .Z47(Z[46]),
    .Z48(Z[47]),
    .Z49(Z[48]),
    .Z50(Z[49]),
    .Z51(Z[50]),
    .Z52(Z[51]),
    .Z53(Z[52]),
    .Z54(Z[53]),
    .Z55(Z[54]),
    .Z56(Z[55])
  );
endmodule

module NX_PLL_U_WRAP(R, REF, FBK, OSC, VCO, LDFO, REFO, PLL_LOCKED, PLL_LOCKEDA, ARST_CAL, CLK_CAL, CLK_CAL_DIV, CAL_LOCKED, EXT_CAL_LOCKED, CAL, CLK_DIVD, EXT_CAL, CLK_DIV);
    input ARST_CAL;
    output [4:0] CAL;
    output CAL_LOCKED;
    input CLK_CAL;
    output CLK_CAL_DIV;
    output [3:0] CLK_DIV;
    output [4:0] CLK_DIVD;
    input [4:0] EXT_CAL;
    input EXT_CAL_LOCKED;
    input FBK;
    output LDFO;
    output OSC;
    output PLL_LOCKED;
    output PLL_LOCKEDA;
    input R;
    input REF;
    output REFO;
    output VCO;
    parameter cal_delay = 6'b011011;
    parameter cal_div = 4'b0111;
    parameter clk_cal_sel = 2'b01;
    parameter clk_outdiv1 = 3'b000;
    parameter clk_outdiv2 = 3'b000;
    parameter clk_outdiv3 = 3'b000;
    parameter clk_outdiv4 = 3'b000;
    parameter clk_outdivd1 = 4'b0000;
    parameter clk_outdivd2 = 4'b0000;
    parameter clk_outdivd3 = 4'b0000;
    parameter clk_outdivd4 = 4'b0000;
    parameter clk_outdivd5 = 4'b0000;
    parameter ext_fbk_on = 1'b0;
    parameter fbk_delay = 6'b000000;
    parameter fbk_delay_on = 1'b0;
    parameter fbk_intdiv = 7'b0000000;
    parameter location = "";
    parameter pll_cpump = 4'b0000;
    parameter pll_lock = 4'b0000;
    parameter pll_lpf_cap = 4'b0000;
    parameter pll_lpf_res = 4'b0000;
    parameter pll_odf = 2'b00;
    parameter ref_intdiv = 5'b00000;
    parameter ref_osc_on = 1'b0;
    parameter use_cal = 1'b0;
    parameter use_pll = 1'b1;

  NX_PLL_U #(
    .cal_delay(cal_delay),
    .cal_div(cal_div),
    .clk_cal_sel(clk_cal_sel),
    .clk_outdiv1(clk_outdiv1),
    .clk_outdiv2(clk_outdiv2),
    .clk_outdiv3(clk_outdiv3),
    .clk_outdiv4(clk_outdiv4),
    .clk_outdivd1(clk_outdivd1),
    .clk_outdivd2(clk_outdivd2),
    .clk_outdivd3(clk_outdivd3),
    .clk_outdivd4(clk_outdivd4),
    .clk_outdivd5(clk_outdivd5),
    .ext_fbk_on(ext_fbk_on),
    .fbk_delay(fbk_delay),
    .fbk_delay_on(fbk_delay_on),
    .fbk_intdiv(fbk_intdiv),
    .location(location),
    .pll_cpump(pll_cpump),
    .pll_lock(pll_lock),
    .pll_lpf_cap(pll_lpf_cap),
    .pll_lpf_res(pll_lpf_res),
    .pll_odf(pll_odf),
    .ref_intdiv(ref_intdiv),
    .ref_osc_on(ref_osc_on),
    .use_cal(use_cal),
    .use_pll(use_pll)
  ) _TECHMAP_REPLACE_ (
    .ARST_CAL(ARST_CAL),
    .CAL1(CAL[0]),
    .CAL2(CAL[1]),
    .CAL3(CAL[2]),
    .CAL4(CAL[3]),
    .CAL5(CAL[4]),
    .CAL_LOCKED(CAL_LOCKED),
    .CLK_CAL(CLK_CAL),
    .CLK_CAL_DIV(CLK_CAL_DIV),
    .CLK_DIV1(CLK_DIV[0]),
    .CLK_DIV2(CLK_DIV[1]),
    .CLK_DIV3(CLK_DIV[2]),
    .CLK_DIV4(CLK_DIV[3]),
    .CLK_DIVD1(CLK_DIVD[0]),
    .CLK_DIVD2(CLK_DIVD[1]),
    .CLK_DIVD3(CLK_DIVD[2]),
    .CLK_DIVD4(CLK_DIVD[3]),
    .CLK_DIVD5(CLK_DIVD[4]),
    .EXT_CAL1(EXT_CAL[0]),
    .EXT_CAL2(EXT_CAL[1]),
    .EXT_CAL3(EXT_CAL[2]),
    .EXT_CAL4(EXT_CAL[3]),
    .EXT_CAL5(EXT_CAL[4]),
    .EXT_CAL_LOCKED(EXT_CAL_LOCKED),
    .FBK(FBK),
    .LDFO(LDFO),
    .OSC(OSC),
    .PLL_LOCKED(PLL_LOCKED),
    .PLL_LOCKEDA(PLL_LOCKEDA),
    .R(R),
    .REF(REF),
    .REFO(REFO),
    .VCO(VCO)
  );
endmodule

module NX_RFBDP_U_WRAP(WCK, WE, WEA, I, O, RA, WA);
    input [17:0] I;
    output [17:0] O;
    input [4:0] RA;
    input [4:0] WA;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter wck_edge = 1'b0;

  NX_RFB_U #(
    .mode(0),
    .mem_ctxt(mem_ctxt),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .RA1(RA[0]),
    .RA2(RA[1]),
    .RA3(RA[2]),
    .RA4(RA[3]),
    .RA5(RA[4]),
    .RA6(),
    .RA7(),
    .RA8(),
    .RA9(),
    .RA10(),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(),
    .WE(WE),
    .WEA(WEA)
  );

endmodule

module NX_RFBSP_U_WRAP(WCK, WE, WEA, I, O, WA);
    input [17:0] I;
    output [17:0] O;
    input [4:0] WA;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter wck_edge = 1'b0;

  NX_RFB_U #(
    .mode(1),
    .mem_ctxt(mem_ctxt),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .RA1(),
    .RA2(),
    .RA3(),
    .RA4(),
    .RA5(),
    .RA6(),
    .RA7(),
    .RA8(),
    .RA9(),
    .RA10(),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(),
    .WE(WE),
    .WEA(WEA)
  );
endmodule

module NX_XRFB_64x18(WCK, WE, WEA, I, O, RA, WA);
    input [17:0] I;
    output [17:0] O;
    input [5:0] RA;
    input [5:0] WA;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter wck_edge = 1'b0;

  NX_RFB_U #(
    .mode(2),
    .mem_ctxt(mem_ctxt),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .RA1(RA[0]),
    .RA2(RA[1]),
    .RA3(RA[2]),
    .RA4(RA[3]),
    .RA5(RA[4]),
    .RA6(RA[5]),
    .RA7(),
    .RA8(),
    .RA9(),
    .RA10(),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(WA[5]),
    .WE(WE),
    .WEA(WEA)
  );
endmodule

module NX_XRFB_32x36(WCK, WE, WEA, I, O, RA, WA);
    input [35:0] I;
    output [35:0] O;
    input [4:0] RA;
    input [4:0] WA;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter wck_edge = 1'b0;

  NX_RFB_U #(
    .mode(3),
    .mem_ctxt(mem_ctxt),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(I[18]),
    .I20(I[19]),
    .I21(I[20]),
    .I22(I[21]),
    .I23(I[22]),
    .I24(I[23]),
    .I25(I[24]),
    .I26(I[25]),
    .I27(I[26]),
    .I28(I[27]),
    .I29(I[28]),
    .I30(I[29]),
    .I31(I[30]),
    .I32(I[31]),
    .I33(I[32]),
    .I34(I[33]),
    .I35(I[34]),
    .I36(I[35]),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .O19(O[18]),
    .O20(O[19]),
    .O21(O[20]),
    .O22(O[21]),
    .O23(O[22]),
    .O24(O[23]),
    .O25(O[24]),
    .O26(O[25]),
    .O27(O[26]),
    .O28(O[27]),
    .O29(O[28]),
    .O30(O[29]),
    .O31(O[30]),
    .O32(O[31]),
    .O33(O[32]),
    .O34(O[33]),
    .O35(O[34]),
    .O36(O[35]),
    .RA1(RA[0]),
    .RA2(RA[1]),
    .RA3(RA[2]),
    .RA4(RA[3]),
    .RA5(RA[4]),
    .RA6(),
    .RA7(),
    .RA8(),
    .RA9(),
    .RA10(),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(),
    .WE(WE),
    .WEA(WEA)
  );
endmodule

module NX_XRFB_2R_1W(WCK, WE, WEA, I, AO, BO, WA, ARA, BRA);
    output [17:0] AO;
    input [4:0] ARA;
    output [17:0] BO;
    input [4:0] BRA;
    input [17:0] I;
    input [4:0] WA;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter wck_edge = 1'b0;

  NX_RFB_U #(
    .mode(32'd4),
    .mem_ctxt(mem_ctxt),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(AO[0]),
    .O2(AO[1]),
    .O3(AO[2]),
    .O4(AO[3]),
    .O5(AO[4]),
    .O6(AO[5]),
    .O7(AO[6]),
    .O8(AO[7]),
    .O9(AO[8]),
    .O10(AO[9]),
    .O11(AO[10]),
    .O12(AO[11]),
    .O13(AO[12]),
    .O14(AO[13]),
    .O15(AO[14]),
    .O16(AO[15]),
    .O17(AO[16]),
    .O18(AO[17]),
    .O19(BO[0]),
    .O20(BO[1]),
    .O21(BO[2]),
    .O22(BO[3]),
    .O23(BO[4]),
    .O24(BO[5]),
    .O25(BO[6]),
    .O26(BO[7]),
    .O27(BO[8]),
    .O28(BO[9]),
    .O29(BO[10]),
    .O30(BO[11]),
    .O31(BO[12]),
    .O32(BO[13]),
    .O33(BO[14]),
    .O34(BO[15]),
    .O35(BO[16]),
    .O36(BO[17]),
    .RA1(ARA[0]),
    .RA2(ARA[1]),
    .RA3(ARA[2]),
    .RA4(ARA[3]),
    .RA5(ARA[4]),
    .RA6(BRA[0]),
    .RA7(BRA[1]),
    .RA8(BRA[2]),
    .RA9(BRA[3]),
    .RA10(BRA[4]),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(),
    .WE(WE),
    .WEA(WEA)
  );
endmodule

module NX_RFB(RCK, WCK, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16, COR, ERR, O1
, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15, O16, RA1, RA2, RA3, RA4, RA5, RA6
, RE, WA1, WA2, WA3, WA4, WA5, WA6, WE);
    output COR;
    output ERR;
    input I1;
    input I10;
    input I11;
    input I12;
    input I13;
    input I14;
    input I15;
    input I16;
    input I2;
    input I3;
    input I4;
    input I5;
    input I6;
    input I7;
    input I8;
    input I9;
    output O1;
    output O10;
    output O11;
    output O12;
    output O13;
    output O14;
    output O15;
    output O16;
    output O2;
    output O3;
    output O4;
    output O5;
    output O6;
    output O7;
    output O8;
    output O9;
    input RA1;
    input RA2;
    input RA3;
    input RA4;
    input RA5;
    input RA6;
    input RCK;
    input RE;
    input WA1;
    input WA2;
    input WA3;
    input WA4;
    input WA5;
    input WA6;
    input WCK;
    input WE;
    parameter addr_mask = 5'b00000;
    parameter mem_ctxt = "";
    parameter rck_edge = 1'b0;
    parameter wck_edge = 1'b0;
    parameter we_mask = 1'b0;
    parameter wea_mask = 1'b0;

  wire [15:0] D;
  wire [15:0] Q;

  NX_RFB_U #(
    .mem_ctxt(mem_ctxt),
    .mode(2),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .WCK(WCK),
    .I1(I1),
    .I2(I2),
    .I3(I3),
    .I4(I4),
    .I5(I5),
    .I6(I6),
    .I7(I7),
    .I8(I8),
    .I9(I9),
    .I10(I10),
    .I11(I11),
    .I12(I12),
    .I13(I13),
    .I14(I14),
    .I15(I15),
    .I16(I16),
    .I17(),
    .I18(),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(D[0]),
    .O2(D[1]),
    .O3(D[2]),
    .O4(D[3]),
    .O5(D[4]),
    .O6(D[5]),
    .O7(D[6]),
    .O8(D[7]),
    .O9(D[8]),
    .O10(D[9]),
    .O11(D[10]),
    .O12(D[11]),
    .O13(D[12]),
    .O14(D[13]),
    .O15(D[14]),
    .O16(D[15]),
    .RA1(RA1),
    .RA2(RA2),
    .RA3(RA3),
    .RA4(RA4),
    .RA5(RA5),
    .RA6(RA6),
    .RA7(),
    .RA8(),
    .RA9(),
    .RA10(),
    .WA1(WA1),
    .WA2(WA2),
    .WA3(WA3),
    .WA4(WA4),
    .WA5(WA5),
    .WA6(WA6),
    .WE(WE),
    .WEA()
  );

  genvar i;
  generate for (i = 0; i < 16; i = i + 1) begin:q_reg
    NX_DFF #(
      .dff_edge(rck_edge),
      .dff_init(1'b0),
      .dff_load(1'b1)
    ) out_reg_i (
        .CK(RCK),
        .I(D[i]),
        .L(RE),
        .R(),
        .O(Q[i])
    );
  end endgenerate;
  assign O1=Q[0];
  assign O2=Q[1];
  assign O3=Q[2];
  assign O4=Q[3];
  assign O5=Q[4];
  assign O6=Q[5];
  assign O7=Q[6];
  assign O8=Q[7];
  assign O9=Q[8];
  assign O10=Q[9];
  assign O11=Q[10];
  assign O12=Q[11];
  assign O13=Q[12];
  assign O14=Q[13];
  assign O15=Q[14];
  assign O16=Q[15];

  assign COR=1'b0;
  assign ERR=1'b0;
endmodule

module NX_FIFO_DPREG(RCK, WCK, WE, WEA, WRSTI, WRSTO, WEQ, RRSTI, RRSTO, REQ, I, O, WAI, WAO, RAI, RAO);
    input [17:0] I;
    output [17:0] O;
    input [5:0] RAI;
    output [5:0] RAO;
    input RCK;
    output REQ;
    input RRSTI;
    output RRSTO;
    input [5:0] WAI;
    output [5:0] WAO;
    input WCK;
    input WE;
    input WEA;
    output WEQ;
    input WRSTI;
    output WRSTO;
    parameter rck_edge = 1'b0;
    parameter read_addr_inv = 6'b000000;
    parameter use_read_arst = 1'b0;
    parameter use_write_arst = 1'b0;
    parameter wck_edge = 1'b0;

  NX_FIFO_U #(
    .mode(0),
    .wck_edge(wck_edge),
    .rck_edge(rck_edge),
    .read_addr_inv(read_addr_inv),
    .use_write_arst(use_write_arst),
    .use_read_arst(use_read_arst)
  ) _TECHMAP_REPLACE_ (
    .RCK(RCK),
    .WCK(WCK),
    .WE(WE),
    .WEA(WEA),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .WRSTI(WRSTI),
    .WAI1(WAI[0]),
    .WAI2(WAI[1]),
    .WAI3(WAI[2]),
    .WAI4(WAI[3]),
    .WAI5(WAI[4]),
    .WAI6(WAI[5]),
    .WAI7(),
    .WRSTO(WRSTO),
    .WAO1(WAO[0]),
    .WAO2(WAO[1]),
    .WAO3(WAO[2]),
    .WAO4(WAO[3]),
    .WAO5(WAO[4]),
    .WAO6(WAO[5]),
    .WEQ1(WEQ),
    .RRSTI(RRSTI),
    .RAI1(RAI[0]),
    .RAI2(RAI[1]),
    .RAI3(RAI[2]),
    .RAI4(RAI[3]),
    .RAI5(RAI[4]),
    .RAI6(RAI[5]),
    .RAI7(),
    .RRSTO(RRSTO),
    .RAO1(RAO[0]),
    .RAO2(RAO[1]),
    .RAO3(RAO[2]),
    .RAO4(RAO[3]),
    .RAO5(RAO[4]),
    .RAO6(RAO[5]),
    .REQ1(REQ)
  );
endmodule

module NX_XFIFO_64x18(RCK, WCK, WE, WEA, WRSTI, RRSTI, I, O, WEQ, REQ, WAI, WAO, RAI, RAO);
    input [17:0] I;
    output [17:0] O;
    input [6:0] RAI;
    output [6:0] RAO;
    input RCK;
    output [1:0] REQ;
    input RRSTI;
    input [6:0] WAI;
    output [6:0] WAO;
    input WCK;
    input WE;
    input WEA;
    output [1:0] WEQ;
    input WRSTI;
    parameter rck_edge = 1'b0;
    parameter read_addr_inv = 7'b0000000;
    parameter use_read_arst = 1'b0;
    parameter use_write_arst = 1'b0;
    parameter wck_edge = 1'b0;

  NX_FIFO_U #(
    .mode(1),
    .wck_edge(wck_edge),
    .rck_edge(rck_edge),
    .read_addr_inv(read_addr_inv),
    .use_write_arst(use_write_arst),
    .use_read_arst(use_read_arst)
  ) _TECHMAP_REPLACE_ (
    .RCK(RCK),
    .WCK(WCK),
    .WE(WE),
    .WEA(WEA),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(),
    .I20(),
    .I21(),
    .I22(),
    .I23(),
    .I24(),
    .I25(),
    .I26(),
    .I27(),
    .I28(),
    .I29(),
    .I30(),
    .I31(),
    .I32(),
    .I33(),
    .I34(),
    .I35(),
    .I36(),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .WRSTI(WRSTI),
    .WAI1(WAI[0]),
    .WAI2(WAI[1]),
    .WAI3(WAI[2]),
    .WAI4(WAI[3]),
    .WAI5(WAI[4]),
    .WAI6(WAI[5]),
    .WAI7(WAI[6]),
    .WAO1(WAO[0]),
    .WAO2(WAO[1]),
    .WAO3(WAO[2]),
    .WAO4(WAO[3]),
    .WAO5(WAO[4]),
    .WAO6(WAO[5]),
    .WAO7(WAO[6]),
    .WEQ1(WEQ[0]),
    .WEQ2(WEQ[1]),
    .RRSTI(RRSTI),
    .RAI1(RAI[0]),
    .RAI2(RAI[1]),
    .RAI3(RAI[2]),
    .RAI4(RAI[3]),
    .RAI5(RAI[4]),
    .RAI6(RAI[5]),
    .RAI7(RAI[6]),
    .RAO1(RAO[0]),
    .RAO2(RAO[1]),
    .RAO3(RAO[2]),
    .RAO4(RAO[3]),
    .RAO5(RAO[4]),
    .RAO6(RAO[5]),
    .RAO7(RAO[6]),
    .REQ1(REQ[0]),
    .REQ2(REQ[1])
  );
endmodule

module NX_XFIFO_32x36(RCK, WCK, WE, WEA, WRSTI, WEQ, RRSTI, REQ, I, O, WAI, WAO, RAI, RAO);
    input [35:0] I;
    output [35:0] O;
    input [5:0] RAI;
    output [5:0] RAO;
    input RCK;
    output REQ;
    input RRSTI;
    input [5:0] WAI;
    output [5:0] WAO;
    input WCK;
    input WE;
    input WEA;
    output WEQ;
    input WRSTI;
    parameter rck_edge = 1'b0;
    parameter read_addr_inv = 7'b0000000;
    parameter use_read_arst = 1'b0;
    parameter use_write_arst = 1'b0;
    parameter wck_edge = 1'b0;

  NX_FIFO_U #(
    .mode(2),
    .wck_edge(wck_edge),
    .rck_edge(rck_edge),
    .read_addr_inv(read_addr_inv),
    .use_write_arst(use_write_arst),
    .use_read_arst(use_read_arst)
  ) _TECHMAP_REPLACE_ (
    .RCK(RCK),
    .WCK(WCK),
    .WE(WE),
    .WEA(WEA),
    .I1(I[0]),
    .I2(I[1]),
    .I3(I[2]),
    .I4(I[3]),
    .I5(I[4]),
    .I6(I[5]),
    .I7(I[6]),
    .I8(I[7]),
    .I9(I[8]),
    .I10(I[9]),
    .I11(I[10]),
    .I12(I[11]),
    .I13(I[12]),
    .I14(I[13]),
    .I15(I[14]),
    .I16(I[15]),
    .I17(I[16]),
    .I18(I[17]),
    .I19(I[18]),
    .I20(I[19]),
    .I21(I[20]),
    .I22(I[21]),
    .I23(I[22]),
    .I24(I[23]),
    .I25(I[24]),
    .I26(I[25]),
    .I27(I[26]),
    .I28(I[27]),
    .I29(I[28]),
    .I30(I[29]),
    .I31(I[30]),
    .I32(I[31]),
    .I33(I[32]),
    .I34(I[33]),
    .I35(I[34]),
    .I36(I[35]),
    .O1(O[0]),
    .O2(O[1]),
    .O3(O[2]),
    .O4(O[3]),
    .O5(O[4]),
    .O6(O[5]),
    .O7(O[6]),
    .O8(O[7]),
    .O9(O[8]),
    .O10(O[9]),
    .O11(O[10]),
    .O12(O[11]),
    .O13(O[12]),
    .O14(O[13]),
    .O15(O[14]),
    .O16(O[15]),
    .O17(O[16]),
    .O18(O[17]),
    .O19(O[18]),
    .O20(O[19]),
    .O21(O[20]),
    .O22(O[21]),
    .O23(O[22]),
    .O24(O[23]),
    .O25(O[24]),
    .O26(O[25]),
    .O27(O[26]),
    .O28(O[27]),
    .O29(O[28]),
    .O30(O[29]),
    .O31(O[30]),
    .O32(O[31]),
    .O33(O[32]),
    .O34(O[33]),
    .O35(O[34]),
    .O36(O[35]),
    .WRSTI(WRSTI),
    .WAI1(WAI[0]),
    .WAI2(WAI[1]),
    .WAI3(WAI[2]),
    .WAI4(WAI[3]),
    .WAI5(WAI[4]),
    .WAI6(WAI[5]),
    .WAI7(),
    .WAO1(WAO[0]),
    .WAO2(WAO[1]),
    .WAO3(WAO[2]),
    .WAO4(WAO[3]),
    .WAO5(WAO[4]),
    .WAO6(WAO[5]),
    .WEQ1(WEQ),
    .RRSTI(RRSTI),
    .RAI1(RAI[0]),
    .RAI2(RAI[1]),
    .RAI3(RAI[2]),
    .RAI4(RAI[3]),
    .RAI5(RAI[4]),
    .RAI6(RAI[5]),
    .RAI7(),
    .RAO1(RAO[0]),
    .RAO2(RAO[1]),
    .RAO3(RAO[2]),
    .RAO4(RAO[3]),
    .RAO5(RAO[4]),
    .RAO6(RAO[5]),
    .REQ1(REQ)
  );
endmodule

//TODO
module ACC84_2DSP(clk, rst, X, Z);
    input [83:0] X;
    output [84:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 2;
endmodule

//TODO
module ACC92_2DSP(clk, rst, X, Z);
    input [55:0] X;
    output [91:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 2;
endmodule

//TODO
module ACC98_2DSP(clk, rst, X, Z);
    input [55:0] X;
    output [97:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 2;
endmodule

//TODO
module ADD84_1DSP_2CYCLES(clk, rst, X, Y, Z);
    input [41:0] X;
    input [41:0] Y;
    output [84:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module ADD84_2DSP(clk, rst, X, Y, Z);
    input [83:0] X;
    input [83:0] Y;
    output [84:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module SMACC24x18_1DSP(clk, rst, A, B, Z);
    input [23:0] A;
    input [17:0] B;
    output [55:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 1;
endmodule

//TODO
module SMACC24x32_2DSP(clk, rst, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [55:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 1;
endmodule

//TODO
module SMACC24x32_enable_2DSP(clk, rst, we, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [55:0] Z;
    input clk;
    input rst;
    input we;
    parameter STAGE_1 = "false";
    parameter STAGE_2 = "false";
    parameter STAGE_3 = "false";
    parameter STAGE_4 = "false";
endmodule

//TODO
module SMUL24x32_2DSP(clk, rst, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [54:0] Z;
    input clk;
    input rst;
    parameter g_pipe = 1;
endmodule

//TODO
module SMUL24x32_2DSP_ACC_2DSP(clk, rst, we, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [97:0] Z;
    input clk;
    input rst;
    input we;
    parameter STAGE_1 = "false";
    parameter STAGE_2 = "false";
    parameter STAGE_3 = "false";
endmodule

//TODO
module SMUL47x35_4DSP(clk, rst, A, B, Z);
    input [46:0] A;
    input [34:0] B;
    output [80:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMADD24_2DSP(clk, rst, A, B, C, Z);
    input [23:0] A;
    input [31:0] B;
    input [55:0] C;
    output [55:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL24x32_1DSP_2CYCLES(clk, rst, A, B, Z);
    input [23:0] A;
    input [15:0] B;
    output [55:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL24x32_2DSP(clk, rst, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [55:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL24x36_1DSP_2CYCLES(clk, rst, A, B, Z);
    input [23:0] A;
    input [17:0] B;
    output [59:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL24x36_2DSP(clk, rst, A, B, Z);
    input [23:0] A;
    input [35:0] B;
    output [59:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL48x36_1DSP_4CYCLES(clk, rst, A, B, Z);
    input [23:0] A;
    input [17:0] B;
    output [83:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module UMUL48x36_4DSP(clk, rst, A, B, Z);
    input [47:0] A;
    input [35:0] B;
    output [83:0] Z;
    input clk;
    input rst;
    parameter piped = "true";
endmodule

//TODO
module NX_HSSL_U_FULL(hssl_clk_user_tx_i, hssl_clk_user_rx_i, hssl_clk_ref_i, hssl_clock_o, hssl_rclock_o, usr_dyn_cfg_en_i, usr_dyn_cfg_calibration_cs_n_i, usr_dyn_cfg_we_n_i, usr_dyn_cfg_wdata_sel_i, usr_pll_pma_rst_n_i, usr_pll_pma_pwr_down_n_i, usr_main_rst_n_i, usr_pll_lock_o, usr_pll_pma_lock_analog_o, usr_pll_ckfb_lock_o, usr_calibrate_pma_out_o, usr_main_async_debug_ack_i, usr_main_async_debug_req_o, scan_en_i, usr_tx0_ctrl_replace_en_i, usr_tx0_rst_n_i
, usr_tx0_busy_o, usr_tx0_ctrl_invalid_k_o, usr_tx0_ctrl_driver_pwrdwn_n_i, usr_tx0_pma_clk_en_i, usr_tx0_pma_tx_clk_o, usr_rx0_ctrl_dscr_en_i, usr_rx0_ctrl_dec_en_i, usr_rx0_ctrl_align_en_i, usr_rx0_ctrl_align_sync_i, usr_rx0_ctrl_replace_en_i, usr_rx0_ctrl_el_buff_rst_i, usr_rx0_rst_n_i, usr_rx0_pma_rst_n_i, usr_rx0_pma_m_eye_rst_i, usr_rx0_pma_pwr_down_n_i, usr_rx0_ctrl_char_is_aligned_o, usr_rx0_ctrl_valid_realign_o, usr_rx0_busy_o, usr_rx0_pma_loss_of_signal_o, usr_rx0_pma_ll_fast_locked_o, usr_rx0_pma_ll_slow_locked_o
, usr_rx0_pma_pll_lock_o, usr_rx0_pma_pll_lock_track_o, usr_tx1_ctrl_replace_en_i, usr_tx1_rst_n_i, usr_tx1_busy_o, usr_tx1_ctrl_invalid_k_o, usr_tx1_ctrl_driver_pwrdwn_n_i, usr_tx1_pma_clk_en_i, usr_tx1_pma_tx_clk_o, usr_rx1_ctrl_dscr_en_i, usr_rx1_ctrl_dec_en_i, usr_rx1_ctrl_align_en_i, usr_rx1_ctrl_align_sync_i, usr_rx1_ctrl_replace_en_i, usr_rx1_ctrl_el_buff_rst_i, usr_rx1_rst_n_i, usr_rx1_pma_rst_n_i, usr_rx1_pma_m_eye_rst_i, usr_rx1_pma_pwr_down_n_i, usr_rx1_ctrl_char_is_aligned_o, usr_rx1_ctrl_valid_realign_o
, usr_rx1_busy_o, usr_rx1_pma_loss_of_signal_o, usr_rx1_pma_ll_fast_locked_o, usr_rx1_pma_ll_slow_locked_o, usr_rx1_pma_pll_lock_o, usr_rx1_pma_pll_lock_track_o, usr_tx2_ctrl_replace_en_i, usr_tx2_rst_n_i, usr_tx2_busy_o, usr_tx2_ctrl_invalid_k_o, usr_tx2_ctrl_driver_pwrdwn_n_i, usr_tx2_pma_clk_en_i, usr_tx2_pma_tx_clk_o, usr_rx2_ctrl_dscr_en_i, usr_rx2_ctrl_dec_en_i, usr_rx2_ctrl_align_en_i, usr_rx2_ctrl_align_sync_i, usr_rx2_ctrl_replace_en_i, usr_rx2_ctrl_el_buff_rst_i, usr_rx2_rst_n_i, usr_rx2_pma_rst_n_i
, usr_rx2_pma_m_eye_rst_i, usr_rx2_pma_pwr_down_n_i, usr_rx2_ctrl_char_is_aligned_o, usr_rx2_ctrl_valid_realign_o, usr_rx2_busy_o, usr_rx2_pma_loss_of_signal_o, usr_rx2_pma_ll_fast_locked_o, usr_rx2_pma_ll_slow_locked_o, usr_rx2_pma_pll_lock_o, usr_rx2_pma_pll_lock_track_o, usr_tx3_ctrl_replace_en_i, usr_tx3_rst_n_i, usr_tx3_busy_o, usr_tx3_ctrl_invalid_k_o, usr_tx3_ctrl_driver_pwrdwn_n_i, usr_tx3_pma_clk_en_i, usr_tx3_pma_tx_clk_o, usr_rx3_ctrl_dscr_en_i, usr_rx3_ctrl_dec_en_i, usr_rx3_ctrl_align_en_i, usr_rx3_ctrl_align_sync_i
, usr_rx3_ctrl_replace_en_i, usr_rx3_ctrl_el_buff_rst_i, usr_rx3_rst_n_i, usr_rx3_pma_rst_n_i, usr_rx3_pma_m_eye_rst_i, usr_rx3_pma_pwr_down_n_i, usr_rx3_ctrl_char_is_aligned_o, usr_rx3_ctrl_valid_realign_o, usr_rx3_busy_o, usr_rx3_pma_loss_of_signal_o, usr_rx3_pma_ll_fast_locked_o, usr_rx3_pma_ll_slow_locked_o, usr_rx3_pma_pll_lock_o, usr_rx3_pma_pll_lock_track_o, usr_tx0_ctrl_enc_en_i, usr_tx0_ctrl_char_is_k_i, usr_tx0_ctrl_scr_en_i, usr_tx0_ctrl_end_of_multiframe_i, usr_tx0_ctrl_end_of_frame_i, usr_tx0_data_i, usr_rx0_data_o
, usr_rx0_ctrl_ovs_bit_sel_i, usr_rx0_ctrl_char_is_comma_o, usr_rx0_ctrl_char_is_k_o, usr_rx0_ctrl_not_in_table_o, usr_rx0_ctrl_disp_err_o, usr_rx0_ctrl_char_is_a_o, usr_rx0_ctrl_char_is_f_o, usr_rx0_test_o, usr_tx1_ctrl_enc_en_i, usr_tx1_ctrl_char_is_k_i, usr_tx1_ctrl_scr_en_i, usr_tx1_ctrl_end_of_multiframe_i, usr_tx1_ctrl_end_of_frame_i, usr_tx1_data_i, usr_rx1_data_o, usr_rx1_ctrl_ovs_bit_sel_i, usr_rx1_ctrl_char_is_comma_o, usr_rx1_ctrl_char_is_k_o, usr_rx1_ctrl_not_in_table_o, usr_rx1_ctrl_disp_err_o, usr_rx1_ctrl_char_is_a_o
, usr_rx1_ctrl_char_is_f_o, usr_rx1_test_o, usr_tx2_ctrl_enc_en_i, usr_tx2_ctrl_char_is_k_i, usr_tx2_ctrl_scr_en_i, usr_tx2_ctrl_end_of_multiframe_i, usr_tx2_ctrl_end_of_frame_i, usr_tx2_data_i, usr_rx2_data_o, usr_rx2_ctrl_ovs_bit_sel_i, usr_rx2_ctrl_char_is_comma_o, usr_rx2_ctrl_char_is_k_o, usr_rx2_ctrl_not_in_table_o, usr_rx2_ctrl_disp_err_o, usr_rx2_ctrl_char_is_a_o, usr_rx2_ctrl_char_is_f_o, usr_rx2_test_o, usr_tx3_ctrl_enc_en_i, usr_tx3_ctrl_char_is_k_i, usr_tx3_ctrl_scr_en_i, usr_tx3_ctrl_end_of_multiframe_i
, usr_tx3_ctrl_end_of_frame_i, usr_tx3_data_i, usr_rx3_data_o, usr_rx3_ctrl_ovs_bit_sel_i, usr_rx3_ctrl_char_is_comma_o, usr_rx3_ctrl_char_is_k_o, usr_rx3_ctrl_not_in_table_o, usr_rx3_ctrl_disp_err_o, usr_rx3_ctrl_char_is_a_o, usr_rx3_ctrl_char_is_f_o, usr_rx3_test_o, usr_dyn_cfg_addr_i, usr_dyn_cfg_wdata_i, usr_main_async_debug_lane_sel_i, usr_main_rx_pma_ll_out_o, scan_in_i, scan_out_o, usr_rx0_ctrl_debug_sel_i, usr_rx1_ctrl_debug_sel_i, usr_rx2_ctrl_debug_sel_i, usr_rx3_ctrl_debug_sel_i
, usr_dyn_cfg_lane_cs_n_i);
    input hssl_clk_ref_i;
    input hssl_clk_user_rx_i;
    input hssl_clk_user_tx_i;
    output hssl_clock_o;
    output hssl_rclock_o;
    input scan_en_i;
    input [7:0] scan_in_i;
    output [7:0] scan_out_o;
    output usr_calibrate_pma_out_o;
    input [3:0] usr_dyn_cfg_addr_i;
    input usr_dyn_cfg_calibration_cs_n_i;
    input usr_dyn_cfg_en_i;
    input [3:0] usr_dyn_cfg_lane_cs_n_i;
    input [11:0] usr_dyn_cfg_wdata_i;
    input usr_dyn_cfg_wdata_sel_i;
    input usr_dyn_cfg_we_n_i;
    input usr_main_async_debug_ack_i;
    input [1:0] usr_main_async_debug_lane_sel_i;
    output usr_main_async_debug_req_o;
    input usr_main_rst_n_i;
    output [19:0] usr_main_rx_pma_ll_out_o;
    output usr_pll_ckfb_lock_o;
    output usr_pll_lock_o;
    output usr_pll_pma_lock_analog_o;
    input usr_pll_pma_pwr_down_n_i;
    input usr_pll_pma_rst_n_i;
    output usr_rx0_busy_o;
    input usr_rx0_ctrl_align_en_i;
    input usr_rx0_ctrl_align_sync_i;
    output [7:0] usr_rx0_ctrl_char_is_a_o;
    output usr_rx0_ctrl_char_is_aligned_o;
    output [7:0] usr_rx0_ctrl_char_is_comma_o;
    output [7:0] usr_rx0_ctrl_char_is_f_o;
    output [7:0] usr_rx0_ctrl_char_is_k_o;
    input [2:0] usr_rx0_ctrl_debug_sel_i;
    input usr_rx0_ctrl_dec_en_i;
    output [7:0] usr_rx0_ctrl_disp_err_o;
    input usr_rx0_ctrl_dscr_en_i;
    input usr_rx0_ctrl_el_buff_rst_i;
    output [7:0] usr_rx0_ctrl_not_in_table_o;
    input [1:0] usr_rx0_ctrl_ovs_bit_sel_i;
    input usr_rx0_ctrl_replace_en_i;
    output usr_rx0_ctrl_valid_realign_o;
    output [63:0] usr_rx0_data_o;
    output usr_rx0_pma_ll_fast_locked_o;
    output usr_rx0_pma_ll_slow_locked_o;
    output usr_rx0_pma_loss_of_signal_o;
    input usr_rx0_pma_m_eye_rst_i;
    output usr_rx0_pma_pll_lock_o;
    output usr_rx0_pma_pll_lock_track_o;
    input usr_rx0_pma_pwr_down_n_i;
    input usr_rx0_pma_rst_n_i;
    input usr_rx0_rst_n_i;
    output [7:0] usr_rx0_test_o;
    output usr_rx1_busy_o;
    input usr_rx1_ctrl_align_en_i;
    input usr_rx1_ctrl_align_sync_i;
    output [7:0] usr_rx1_ctrl_char_is_a_o;
    output usr_rx1_ctrl_char_is_aligned_o;
    output [7:0] usr_rx1_ctrl_char_is_comma_o;
    output [7:0] usr_rx1_ctrl_char_is_f_o;
    output [7:0] usr_rx1_ctrl_char_is_k_o;
    input [2:0] usr_rx1_ctrl_debug_sel_i;
    input usr_rx1_ctrl_dec_en_i;
    output [7:0] usr_rx1_ctrl_disp_err_o;
    input usr_rx1_ctrl_dscr_en_i;
    input usr_rx1_ctrl_el_buff_rst_i;
    output [7:0] usr_rx1_ctrl_not_in_table_o;
    input [1:0] usr_rx1_ctrl_ovs_bit_sel_i;
    input usr_rx1_ctrl_replace_en_i;
    output usr_rx1_ctrl_valid_realign_o;
    output [63:0] usr_rx1_data_o;
    output usr_rx1_pma_ll_fast_locked_o;
    output usr_rx1_pma_ll_slow_locked_o;
    output usr_rx1_pma_loss_of_signal_o;
    input usr_rx1_pma_m_eye_rst_i;
    output usr_rx1_pma_pll_lock_o;
    output usr_rx1_pma_pll_lock_track_o;
    input usr_rx1_pma_pwr_down_n_i;
    input usr_rx1_pma_rst_n_i;
    input usr_rx1_rst_n_i;
    output [7:0] usr_rx1_test_o;
    output usr_rx2_busy_o;
    input usr_rx2_ctrl_align_en_i;
    input usr_rx2_ctrl_align_sync_i;
    output [7:0] usr_rx2_ctrl_char_is_a_o;
    output usr_rx2_ctrl_char_is_aligned_o;
    output [7:0] usr_rx2_ctrl_char_is_comma_o;
    output [7:0] usr_rx2_ctrl_char_is_f_o;
    output [7:0] usr_rx2_ctrl_char_is_k_o;
    input [2:0] usr_rx2_ctrl_debug_sel_i;
    input usr_rx2_ctrl_dec_en_i;
    output [7:0] usr_rx2_ctrl_disp_err_o;
    input usr_rx2_ctrl_dscr_en_i;
    input usr_rx2_ctrl_el_buff_rst_i;
    output [7:0] usr_rx2_ctrl_not_in_table_o;
    input [1:0] usr_rx2_ctrl_ovs_bit_sel_i;
    input usr_rx2_ctrl_replace_en_i;
    output usr_rx2_ctrl_valid_realign_o;
    output [63:0] usr_rx2_data_o;
    output usr_rx2_pma_ll_fast_locked_o;
    output usr_rx2_pma_ll_slow_locked_o;
    output usr_rx2_pma_loss_of_signal_o;
    input usr_rx2_pma_m_eye_rst_i;
    output usr_rx2_pma_pll_lock_o;
    output usr_rx2_pma_pll_lock_track_o;
    input usr_rx2_pma_pwr_down_n_i;
    input usr_rx2_pma_rst_n_i;
    input usr_rx2_rst_n_i;
    output [7:0] usr_rx2_test_o;
    output usr_rx3_busy_o;
    input usr_rx3_ctrl_align_en_i;
    input usr_rx3_ctrl_align_sync_i;
    output [7:0] usr_rx3_ctrl_char_is_a_o;
    output usr_rx3_ctrl_char_is_aligned_o;
    output [7:0] usr_rx3_ctrl_char_is_comma_o;
    output [7:0] usr_rx3_ctrl_char_is_f_o;
    output [7:0] usr_rx3_ctrl_char_is_k_o;
    input [2:0] usr_rx3_ctrl_debug_sel_i;
    input usr_rx3_ctrl_dec_en_i;
    output [7:0] usr_rx3_ctrl_disp_err_o;
    input usr_rx3_ctrl_dscr_en_i;
    input usr_rx3_ctrl_el_buff_rst_i;
    output [7:0] usr_rx3_ctrl_not_in_table_o;
    input [1:0] usr_rx3_ctrl_ovs_bit_sel_i;
    input usr_rx3_ctrl_replace_en_i;
    output usr_rx3_ctrl_valid_realign_o;
    output [63:0] usr_rx3_data_o;
    output usr_rx3_pma_ll_fast_locked_o;
    output usr_rx3_pma_ll_slow_locked_o;
    output usr_rx3_pma_loss_of_signal_o;
    input usr_rx3_pma_m_eye_rst_i;
    output usr_rx3_pma_pll_lock_o;
    output usr_rx3_pma_pll_lock_track_o;
    input usr_rx3_pma_pwr_down_n_i;
    input usr_rx3_pma_rst_n_i;
    input usr_rx3_rst_n_i;
    output [7:0] usr_rx3_test_o;
    output usr_tx0_busy_o;
    input [7:0] usr_tx0_ctrl_char_is_k_i;
    input usr_tx0_ctrl_driver_pwrdwn_n_i;
    input [7:0] usr_tx0_ctrl_enc_en_i;
    input [7:0] usr_tx0_ctrl_end_of_frame_i;
    input [7:0] usr_tx0_ctrl_end_of_multiframe_i;
    output usr_tx0_ctrl_invalid_k_o;
    input usr_tx0_ctrl_replace_en_i;
    input [7:0] usr_tx0_ctrl_scr_en_i;
    input [63:0] usr_tx0_data_i;
    input usr_tx0_pma_clk_en_i;
    output usr_tx0_pma_tx_clk_o;
    input usr_tx0_rst_n_i;
    output usr_tx1_busy_o;
    input [7:0] usr_tx1_ctrl_char_is_k_i;
    input usr_tx1_ctrl_driver_pwrdwn_n_i;
    input [7:0] usr_tx1_ctrl_enc_en_i;
    input [7:0] usr_tx1_ctrl_end_of_frame_i;
    input [7:0] usr_tx1_ctrl_end_of_multiframe_i;
    output usr_tx1_ctrl_invalid_k_o;
    input usr_tx1_ctrl_replace_en_i;
    input [7:0] usr_tx1_ctrl_scr_en_i;
    input [63:0] usr_tx1_data_i;
    input usr_tx1_pma_clk_en_i;
    output usr_tx1_pma_tx_clk_o;
    input usr_tx1_rst_n_i;
    output usr_tx2_busy_o;
    input [7:0] usr_tx2_ctrl_char_is_k_i;
    input usr_tx2_ctrl_driver_pwrdwn_n_i;
    input [7:0] usr_tx2_ctrl_enc_en_i;
    input [7:0] usr_tx2_ctrl_end_of_frame_i;
    input [7:0] usr_tx2_ctrl_end_of_multiframe_i;
    output usr_tx2_ctrl_invalid_k_o;
    input usr_tx2_ctrl_replace_en_i;
    input [7:0] usr_tx2_ctrl_scr_en_i;
    input [63:0] usr_tx2_data_i;
    input usr_tx2_pma_clk_en_i;
    output usr_tx2_pma_tx_clk_o;
    input usr_tx2_rst_n_i;
    output usr_tx3_busy_o;
    input [7:0] usr_tx3_ctrl_char_is_k_i;
    input usr_tx3_ctrl_driver_pwrdwn_n_i;
    input [7:0] usr_tx3_ctrl_enc_en_i;
    input [7:0] usr_tx3_ctrl_end_of_frame_i;
    input [7:0] usr_tx3_ctrl_end_of_multiframe_i;
    output usr_tx3_ctrl_invalid_k_o;
    input usr_tx3_ctrl_replace_en_i;
    input [7:0] usr_tx3_ctrl_scr_en_i;
    input [63:0] usr_tx3_data_i;
    input usr_tx3_pma_clk_en_i;
    output usr_tx3_pma_tx_clk_o;
    input usr_tx3_rst_n_i;
    parameter cfg_dyn_all_rx_pma_m_eye_coarse_ena_i = 1'b0;
    parameter cfg_dyn_all_rx_pma_m_eye_dn_i = 1'b0;
    parameter cfg_dyn_all_rx_pma_m_eye_fine_ena_i = 1'b0;
    parameter cfg_dyn_all_rx_pma_m_eye_i = 1'b0;
    parameter cfg_dyn_all_rx_pma_m_eye_step_i = 4'b0000;
    parameter cfg_dyn_all_rx_pma_m_eye_up_i = 1'b0;
    parameter cfg_dyn_all_rx_pma_threshold_1 = 5'b00000;
    parameter cfg_dyn_all_rx_pma_threshold_2 = 5'b00000;
    parameter cfg_dyn_all_rx_pma_trim_locked_i = 3'b000;
    parameter cfg_dyn_all_rx_pma_trim_mode_i = 2'b00;
    parameter cfg_dyn_all_rx_pma_trim_unlocked_i = 3'b000;
    parameter cfg_dyn_rx0_pma_ctle_cap_p_i = 4'b0000;
    parameter cfg_dyn_rx0_pma_ctle_res_p_i = 4'b0000;
    parameter cfg_dyn_rx0_pma_dfe_idac_tap1_n_i = 6'b000000;
    parameter cfg_dyn_rx0_pma_dfe_idac_tap2_n_i = 6'b000000;
    parameter cfg_dyn_rx0_pma_dfe_idac_tap3_n_i = 6'b000000;
    parameter cfg_dyn_rx0_pma_dfe_idac_tap4_n_i = 6'b000000;
    parameter cfg_dyn_rx0_pma_termination_cmd_i = 6'b000000;
    parameter cfg_dyn_rx1_pma_ctle_cap_p_i = 4'b0000;
    parameter cfg_dyn_rx1_pma_ctle_res_p_i = 4'b0000;
    parameter cfg_dyn_rx1_pma_dfe_idac_tap1_n_i = 6'b000000;
    parameter cfg_dyn_rx1_pma_dfe_idac_tap2_n_i = 6'b000000;
    parameter cfg_dyn_rx1_pma_dfe_idac_tap3_n_i = 6'b000000;
    parameter cfg_dyn_rx1_pma_dfe_idac_tap4_n_i = 6'b000000;
    parameter cfg_dyn_rx1_pma_termination_cmd_i = 6'b000000;
    parameter cfg_dyn_rx2_pma_ctle_cap_p_i = 4'b0000;
    parameter cfg_dyn_rx2_pma_ctle_res_p_i = 4'b0000;
    parameter cfg_dyn_rx2_pma_dfe_idac_tap1_n_i = 6'b000000;
    parameter cfg_dyn_rx2_pma_dfe_idac_tap2_n_i = 6'b000000;
    parameter cfg_dyn_rx2_pma_dfe_idac_tap3_n_i = 6'b000000;
    parameter cfg_dyn_rx2_pma_dfe_idac_tap4_n_i = 6'b000000;
    parameter cfg_dyn_rx2_pma_termination_cmd_i = 6'b000000;
    parameter cfg_dyn_rx3_pma_ctle_cap_p_i = 4'b0000;
    parameter cfg_dyn_rx3_pma_ctle_res_p_i = 4'b0000;
    parameter cfg_dyn_rx3_pma_dfe_idac_tap1_n_i = 6'b000000;
    parameter cfg_dyn_rx3_pma_dfe_idac_tap2_n_i = 6'b000000;
    parameter cfg_dyn_rx3_pma_dfe_idac_tap3_n_i = 6'b000000;
    parameter cfg_dyn_rx3_pma_dfe_idac_tap4_n_i = 6'b000000;
    parameter cfg_dyn_rx3_pma_termination_cmd_i = 6'b000000;
    parameter cfg_dyn_tx0_pma_main_en_i = 6'b000000;
    parameter cfg_dyn_tx0_pma_main_sign_i = 1'b0;
    parameter cfg_dyn_tx0_pma_margin_input_i = 9'b000000000;
    parameter cfg_dyn_tx0_pma_margin_sel_i = 9'b000000000;
    parameter cfg_dyn_tx0_pma_post_en_i = 5'b00000;
    parameter cfg_dyn_tx0_pma_post_sel_i = 8'b00000000;
    parameter cfg_dyn_tx0_pma_post_sign_i = 1'b0;
    parameter cfg_dyn_tx0_pma_pre_en_i = 1'b0;
    parameter cfg_dyn_tx0_pma_pre_sel_i = 4'b0000;
    parameter cfg_dyn_tx0_pma_pre_sign_i = 1'b0;
    parameter cfg_dyn_tx1_pma_main_en_i = 6'b000000;
    parameter cfg_dyn_tx1_pma_main_sign_i = 1'b0;
    parameter cfg_dyn_tx1_pma_margin_input_i = 9'b000000000;
    parameter cfg_dyn_tx1_pma_margin_sel_i = 9'b000000000;
    parameter cfg_dyn_tx1_pma_post_en_i = 5'b00000;
    parameter cfg_dyn_tx1_pma_post_sel_i = 8'b00000000;
    parameter cfg_dyn_tx1_pma_post_sign_i = 1'b0;
    parameter cfg_dyn_tx1_pma_pre_en_i = 1'b0;
    parameter cfg_dyn_tx1_pma_pre_sel_i = 4'b0000;
    parameter cfg_dyn_tx1_pma_pre_sign_i = 1'b0;
    parameter cfg_dyn_tx2_pma_main_en_i = 6'b000000;
    parameter cfg_dyn_tx2_pma_main_sign_i = 1'b0;
    parameter cfg_dyn_tx2_pma_margin_input_i = 9'b000000000;
    parameter cfg_dyn_tx2_pma_margin_sel_i = 9'b000000000;
    parameter cfg_dyn_tx2_pma_post_en_i = 5'b00000;
    parameter cfg_dyn_tx2_pma_post_sel_i = 8'b00000000;
    parameter cfg_dyn_tx2_pma_post_sign_i = 1'b0;
    parameter cfg_dyn_tx2_pma_pre_en_i = 1'b0;
    parameter cfg_dyn_tx2_pma_pre_sel_i = 4'b0000;
    parameter cfg_dyn_tx2_pma_pre_sign_i = 1'b0;
    parameter cfg_dyn_tx3_pma_main_en_i = 6'b000000;
    parameter cfg_dyn_tx3_pma_main_sign_i = 1'b0;
    parameter cfg_dyn_tx3_pma_margin_input_i = 9'b000000000;
    parameter cfg_dyn_tx3_pma_margin_sel_i = 9'b000000000;
    parameter cfg_dyn_tx3_pma_post_en_i = 5'b00000;
    parameter cfg_dyn_tx3_pma_post_sel_i = 8'b00000000;
    parameter cfg_dyn_tx3_pma_post_sign_i = 1'b0;
    parameter cfg_dyn_tx3_pma_pre_en_i = 1'b0;
    parameter cfg_dyn_tx3_pma_pre_sel_i = 4'b0000;
    parameter cfg_dyn_tx3_pma_pre_sign_i = 1'b0;
    parameter cfg_main_clk_to_fabric_div_en_i = 1'b0;
    parameter cfg_main_clk_to_fabric_div_mode_i = 1'b0;
    parameter cfg_main_clk_to_fabric_sel_i = 1'b0;
    parameter cfg_main_rclk_to_fabric_sel_i = 2'b00;
    parameter cfg_main_use_only_usr_clock_i = 1'b0;
    parameter cfg_pcs_ovs_en_i = 1'b0;
    parameter cfg_pcs_ovs_mode_i = 1'b0;
    parameter cfg_pcs_pll_lock_ppm_i = 3'b000;
    parameter cfg_pcs_word_len_i = 2'b00;
    parameter cfg_pll_pma_ckref_ext_i = 1'b0;
    parameter cfg_pll_pma_cpump_i = 4'b0000;
    parameter cfg_pll_pma_divl_i = 2'b00;
    parameter cfg_pll_pma_divm_i = 1'b0;
    parameter cfg_pll_pma_divn_i = 2'b00;
    parameter cfg_pll_pma_gbx_en_i = 1'b0;
    parameter cfg_pll_pma_int_data_len_i = 1'b0;
    parameter cfg_pll_pma_lvds_en_i = 1'b0;
    parameter cfg_pll_pma_lvds_mux_i = 1'b0;
    parameter cfg_pll_pma_mux_ckref_i = 1'b0;
    parameter cfg_rx0_gearbox_en_i = 1'b0;
    parameter cfg_rx0_gearbox_mode_i = 1'b0;
    parameter cfg_rx0_pcs_8b_dscr_sel_i = 1'b0;
    parameter cfg_rx0_pcs_align_bypass_i = 1'b0;
    parameter cfg_rx0_pcs_buffers_bypass_i = 1'b0;
    parameter cfg_rx0_pcs_buffers_use_cdc_i = 1'b0;
    parameter cfg_rx0_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_rx0_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_rx0_pcs_comma_mask_i = 10'b0000000000;
    parameter cfg_rx0_pcs_debug_en_i = 1'b0;
    parameter cfg_rx0_pcs_dec_bypass_i = 1'b0;
    parameter cfg_rx0_pcs_dscr_bypass_i = 1'b0;
    parameter cfg_rx0_pcs_el_buff_diff_bef_comp_i = 4'b0000;
    parameter cfg_rx0_pcs_el_buff_max_comp_i = 4'b0000;
    parameter cfg_rx0_pcs_el_buff_only_one_skp_i = 1'b0;
    parameter cfg_rx0_pcs_el_buff_skp_char_0_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_char_1_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_char_2_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_char_3_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_header_0_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_header_1_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_header_2_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_header_3_i = 9'b000000000;
    parameter cfg_rx0_pcs_el_buff_skp_header_size_i = 2'b00;
    parameter cfg_rx0_pcs_el_buff_skp_seq_size_i = 2'b00;
    parameter cfg_rx0_pcs_fsm_sel_i = 2'b00;
    parameter cfg_rx0_pcs_fsm_watchdog_en_i = 1'b0;
    parameter cfg_rx0_pcs_loopback_i = 1'b0;
    parameter cfg_rx0_pcs_m_comma_en_i = 1'b0;
    parameter cfg_rx0_pcs_m_comma_val_i = 10'b0000000000;
    parameter cfg_rx0_pcs_nb_comma_bef_realign_i = 2'b00;
    parameter cfg_rx0_pcs_p_comma_en_i = 1'b0;
    parameter cfg_rx0_pcs_p_comma_val_i = 10'b0000000000;
    parameter cfg_rx0_pcs_polarity_i = 1'b0;
    parameter cfg_rx0_pcs_protocol_size_i = 1'b0;
    parameter cfg_rx0_pcs_replace_bypass_i = 1'b0;
    parameter cfg_rx0_pcs_sync_supported_i = 1'b0;
    parameter cfg_rx0_pma_cdr_cp_i = 4'b0000;
    parameter cfg_rx0_pma_clk_pos_i = 1'b0;
    parameter cfg_rx0_pma_coarse_ppm_i = 3'b000;
    parameter cfg_rx0_pma_ctrl_term_i = 6'b000000;
    parameter cfg_rx0_pma_dco_divl_i = 2'b00;
    parameter cfg_rx0_pma_dco_divm_i = 1'b0;
    parameter cfg_rx0_pma_dco_divn_i = 2'b00;
    parameter cfg_rx0_pma_dco_reg_res_i = 2'b00;
    parameter cfg_rx0_pma_dco_vref_sel_i = 1'b0;
    parameter cfg_rx0_pma_fine_ppm_i = 3'b000;
    parameter cfg_rx0_pma_loopback_i = 1'b0;
    parameter cfg_rx0_pma_m_eye_ppm_i = 3'b000;
    parameter cfg_rx0_pma_peak_detect_cmd_i = 2'b00;
    parameter cfg_rx0_pma_peak_detect_on_i = 1'b0;
    parameter cfg_rx0_pma_pll_cpump_n_i = 3'b000;
    parameter cfg_rx0_pma_pll_divf_en_n_i = 1'b0;
    parameter cfg_rx0_pma_pll_divf_i = 2'b00;
    parameter cfg_rx0_pma_pll_divm_en_n_i = 1'b0;
    parameter cfg_rx0_pma_pll_divm_i = 2'b00;
    parameter cfg_rx0_pma_pll_divn_en_n_i = 1'b0;
    parameter cfg_rx0_pma_pll_divn_i = 1'b0;
    parameter cfg_rx1_gearbox_en_i = 1'b0;
    parameter cfg_rx1_gearbox_mode_i = 1'b0;
    parameter cfg_rx1_pcs_8b_dscr_sel_i = 1'b0;
    parameter cfg_rx1_pcs_align_bypass_i = 1'b0;
    parameter cfg_rx1_pcs_buffers_bypass_i = 1'b0;
    parameter cfg_rx1_pcs_buffers_use_cdc_i = 1'b0;
    parameter cfg_rx1_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_rx1_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_rx1_pcs_comma_mask_i = 10'b0000000000;
    parameter cfg_rx1_pcs_debug_en_i = 1'b0;
    parameter cfg_rx1_pcs_dec_bypass_i = 1'b0;
    parameter cfg_rx1_pcs_dscr_bypass_i = 1'b0;
    parameter cfg_rx1_pcs_el_buff_diff_bef_comp_i = 4'b0000;
    parameter cfg_rx1_pcs_el_buff_max_comp_i = 4'b0000;
    parameter cfg_rx1_pcs_el_buff_only_one_skp_i = 1'b0;
    parameter cfg_rx1_pcs_el_buff_skp_char_0_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_char_1_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_char_2_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_char_3_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_header_0_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_header_1_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_header_2_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_header_3_i = 9'b000000000;
    parameter cfg_rx1_pcs_el_buff_skp_header_size_i = 2'b00;
    parameter cfg_rx1_pcs_el_buff_skp_seq_size_i = 2'b00;
    parameter cfg_rx1_pcs_fsm_sel_i = 2'b00;
    parameter cfg_rx1_pcs_fsm_watchdog_en_i = 1'b0;
    parameter cfg_rx1_pcs_loopback_i = 1'b0;
    parameter cfg_rx1_pcs_m_comma_en_i = 1'b0;
    parameter cfg_rx1_pcs_m_comma_val_i = 10'b0000000000;
    parameter cfg_rx1_pcs_nb_comma_bef_realign_i = 2'b00;
    parameter cfg_rx1_pcs_p_comma_en_i = 1'b0;
    parameter cfg_rx1_pcs_p_comma_val_i = 10'b0000000000;
    parameter cfg_rx1_pcs_polarity_i = 1'b0;
    parameter cfg_rx1_pcs_protocol_size_i = 1'b0;
    parameter cfg_rx1_pcs_replace_bypass_i = 1'b0;
    parameter cfg_rx1_pcs_sync_supported_i = 1'b0;
    parameter cfg_rx1_pma_cdr_cp_i = 4'b0000;
    parameter cfg_rx1_pma_clk_pos_i = 1'b0;
    parameter cfg_rx1_pma_coarse_ppm_i = 3'b000;
    parameter cfg_rx1_pma_ctrl_term_i = 6'b000000;
    parameter cfg_rx1_pma_dco_divl_i = 2'b00;
    parameter cfg_rx1_pma_dco_divm_i = 1'b0;
    parameter cfg_rx1_pma_dco_divn_i = 2'b00;
    parameter cfg_rx1_pma_dco_reg_res_i = 2'b00;
    parameter cfg_rx1_pma_dco_vref_sel_i = 1'b0;
    parameter cfg_rx1_pma_fine_ppm_i = 3'b000;
    parameter cfg_rx1_pma_loopback_i = 1'b0;
    parameter cfg_rx1_pma_m_eye_ppm_i = 3'b000;
    parameter cfg_rx1_pma_peak_detect_cmd_i = 2'b00;
    parameter cfg_rx1_pma_peak_detect_on_i = 1'b0;
    parameter cfg_rx1_pma_pll_cpump_n_i = 3'b000;
    parameter cfg_rx1_pma_pll_divf_en_n_i = 1'b0;
    parameter cfg_rx1_pma_pll_divf_i = 2'b00;
    parameter cfg_rx1_pma_pll_divm_en_n_i = 1'b0;
    parameter cfg_rx1_pma_pll_divm_i = 2'b00;
    parameter cfg_rx1_pma_pll_divn_en_n_i = 1'b0;
    parameter cfg_rx1_pma_pll_divn_i = 1'b0;
    parameter cfg_rx2_gearbox_en_i = 1'b0;
    parameter cfg_rx2_gearbox_mode_i = 1'b0;
    parameter cfg_rx2_pcs_8b_dscr_sel_i = 1'b0;
    parameter cfg_rx2_pcs_align_bypass_i = 1'b0;
    parameter cfg_rx2_pcs_buffers_bypass_i = 1'b0;
    parameter cfg_rx2_pcs_buffers_use_cdc_i = 1'b0;
    parameter cfg_rx2_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_rx2_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_rx2_pcs_comma_mask_i = 10'b0000000000;
    parameter cfg_rx2_pcs_debug_en_i = 1'b0;
    parameter cfg_rx2_pcs_dec_bypass_i = 1'b0;
    parameter cfg_rx2_pcs_dscr_bypass_i = 1'b0;
    parameter cfg_rx2_pcs_el_buff_diff_bef_comp_i = 4'b0000;
    parameter cfg_rx2_pcs_el_buff_max_comp_i = 4'b0000;
    parameter cfg_rx2_pcs_el_buff_only_one_skp_i = 1'b0;
    parameter cfg_rx2_pcs_el_buff_skp_char_0_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_char_1_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_char_2_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_char_3_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_header_0_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_header_1_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_header_2_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_header_3_i = 9'b000000000;
    parameter cfg_rx2_pcs_el_buff_skp_header_size_i = 2'b00;
    parameter cfg_rx2_pcs_el_buff_skp_seq_size_i = 2'b00;
    parameter cfg_rx2_pcs_fsm_sel_i = 2'b00;
    parameter cfg_rx2_pcs_fsm_watchdog_en_i = 1'b0;
    parameter cfg_rx2_pcs_loopback_i = 1'b0;
    parameter cfg_rx2_pcs_m_comma_en_i = 1'b0;
    parameter cfg_rx2_pcs_m_comma_val_i = 10'b0000000000;
    parameter cfg_rx2_pcs_nb_comma_bef_realign_i = 2'b00;
    parameter cfg_rx2_pcs_p_comma_en_i = 1'b0;
    parameter cfg_rx2_pcs_p_comma_val_i = 10'b0000000000;
    parameter cfg_rx2_pcs_polarity_i = 1'b0;
    parameter cfg_rx2_pcs_protocol_size_i = 1'b0;
    parameter cfg_rx2_pcs_replace_bypass_i = 1'b0;
    parameter cfg_rx2_pcs_sync_supported_i = 1'b0;
    parameter cfg_rx2_pma_cdr_cp_i = 4'b0000;
    parameter cfg_rx2_pma_clk_pos_i = 1'b0;
    parameter cfg_rx2_pma_coarse_ppm_i = 3'b000;
    parameter cfg_rx2_pma_ctrl_term_i = 6'b000000;
    parameter cfg_rx2_pma_dco_divl_i = 2'b00;
    parameter cfg_rx2_pma_dco_divm_i = 1'b0;
    parameter cfg_rx2_pma_dco_divn_i = 2'b00;
    parameter cfg_rx2_pma_dco_reg_res_i = 2'b00;
    parameter cfg_rx2_pma_dco_vref_sel_i = 1'b0;
    parameter cfg_rx2_pma_fine_ppm_i = 3'b000;
    parameter cfg_rx2_pma_loopback_i = 1'b0;
    parameter cfg_rx2_pma_m_eye_ppm_i = 3'b000;
    parameter cfg_rx2_pma_peak_detect_cmd_i = 2'b00;
    parameter cfg_rx2_pma_peak_detect_on_i = 1'b0;
    parameter cfg_rx2_pma_pll_cpump_n_i = 3'b000;
    parameter cfg_rx2_pma_pll_divf_en_n_i = 1'b0;
    parameter cfg_rx2_pma_pll_divf_i = 2'b00;
    parameter cfg_rx2_pma_pll_divm_en_n_i = 1'b0;
    parameter cfg_rx2_pma_pll_divm_i = 2'b00;
    parameter cfg_rx2_pma_pll_divn_en_n_i = 1'b0;
    parameter cfg_rx2_pma_pll_divn_i = 1'b0;
    parameter cfg_rx3_gearbox_en_i = 1'b0;
    parameter cfg_rx3_gearbox_mode_i = 1'b0;
    parameter cfg_rx3_pcs_8b_dscr_sel_i = 1'b0;
    parameter cfg_rx3_pcs_align_bypass_i = 1'b0;
    parameter cfg_rx3_pcs_buffers_bypass_i = 1'b0;
    parameter cfg_rx3_pcs_buffers_use_cdc_i = 1'b0;
    parameter cfg_rx3_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_rx3_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_rx3_pcs_comma_mask_i = 10'b0000000000;
    parameter cfg_rx3_pcs_debug_en_i = 1'b0;
    parameter cfg_rx3_pcs_dec_bypass_i = 1'b0;
    parameter cfg_rx3_pcs_dscr_bypass_i = 1'b0;
    parameter cfg_rx3_pcs_el_buff_diff_bef_comp_i = 4'b0000;
    parameter cfg_rx3_pcs_el_buff_max_comp_i = 4'b0000;
    parameter cfg_rx3_pcs_el_buff_only_one_skp_i = 1'b0;
    parameter cfg_rx3_pcs_el_buff_skp_char_0_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_char_1_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_char_2_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_char_3_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_header_0_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_header_1_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_header_2_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_header_3_i = 9'b000000000;
    parameter cfg_rx3_pcs_el_buff_skp_header_size_i = 2'b00;
    parameter cfg_rx3_pcs_el_buff_skp_seq_size_i = 2'b00;
    parameter cfg_rx3_pcs_fsm_sel_i = 2'b00;
    parameter cfg_rx3_pcs_fsm_watchdog_en_i = 1'b0;
    parameter cfg_rx3_pcs_loopback_i = 1'b0;
    parameter cfg_rx3_pcs_m_comma_en_i = 1'b0;
    parameter cfg_rx3_pcs_m_comma_val_i = 10'b0000000000;
    parameter cfg_rx3_pcs_nb_comma_bef_realign_i = 2'b00;
    parameter cfg_rx3_pcs_p_comma_en_i = 1'b0;
    parameter cfg_rx3_pcs_p_comma_val_i = 10'b0000000000;
    parameter cfg_rx3_pcs_polarity_i = 1'b0;
    parameter cfg_rx3_pcs_protocol_size_i = 1'b0;
    parameter cfg_rx3_pcs_replace_bypass_i = 1'b0;
    parameter cfg_rx3_pcs_sync_supported_i = 1'b0;
    parameter cfg_rx3_pma_cdr_cp_i = 4'b0000;
    parameter cfg_rx3_pma_clk_pos_i = 1'b0;
    parameter cfg_rx3_pma_coarse_ppm_i = 3'b000;
    parameter cfg_rx3_pma_ctrl_term_i = 6'b000000;
    parameter cfg_rx3_pma_dco_divl_i = 2'b00;
    parameter cfg_rx3_pma_dco_divm_i = 1'b0;
    parameter cfg_rx3_pma_dco_divn_i = 2'b00;
    parameter cfg_rx3_pma_dco_reg_res_i = 2'b00;
    parameter cfg_rx3_pma_dco_vref_sel_i = 1'b0;
    parameter cfg_rx3_pma_fine_ppm_i = 3'b000;
    parameter cfg_rx3_pma_loopback_i = 1'b0;
    parameter cfg_rx3_pma_m_eye_ppm_i = 3'b000;
    parameter cfg_rx3_pma_peak_detect_cmd_i = 2'b00;
    parameter cfg_rx3_pma_peak_detect_on_i = 1'b0;
    parameter cfg_rx3_pma_pll_cpump_n_i = 3'b000;
    parameter cfg_rx3_pma_pll_divf_en_n_i = 1'b0;
    parameter cfg_rx3_pma_pll_divf_i = 2'b00;
    parameter cfg_rx3_pma_pll_divm_en_n_i = 1'b0;
    parameter cfg_rx3_pma_pll_divm_i = 2'b00;
    parameter cfg_rx3_pma_pll_divn_en_n_i = 1'b0;
    parameter cfg_rx3_pma_pll_divn_i = 1'b0;
    parameter cfg_test_mode_i = 2'b00;
    parameter cfg_tx0_gearbox_en_i = 1'b0;
    parameter cfg_tx0_gearbox_mode_i = 1'b0;
    parameter cfg_tx0_pcs_8b_scr_sel_i = 1'b0;
    parameter cfg_tx0_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_tx0_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_tx0_pcs_enc_bypass_i = 1'b0;
    parameter cfg_tx0_pcs_esistream_fsm_en_i = 1'b0;
    parameter cfg_tx0_pcs_loopback_i = 1'b0;
    parameter cfg_tx0_pcs_polarity_i = 1'b0;
    parameter cfg_tx0_pcs_protocol_size_i = 1'b0;
    parameter cfg_tx0_pcs_replace_bypass_i = 1'b0;
    parameter cfg_tx0_pcs_scr_bypass_i = 1'b0;
    parameter cfg_tx0_pcs_scr_init_i = 17'b00000000000000000;
    parameter cfg_tx0_pcs_sync_supported_i = 1'b0;
    parameter cfg_tx0_pma_clk_pos_i = 1'b0;
    parameter cfg_tx0_pma_loopback_i = 1'b0;
    parameter cfg_tx1_gearbox_en_i = 1'b0;
    parameter cfg_tx1_gearbox_mode_i = 1'b0;
    parameter cfg_tx1_pcs_8b_scr_sel_i = 1'b0;
    parameter cfg_tx1_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_tx1_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_tx1_pcs_enc_bypass_i = 1'b0;
    parameter cfg_tx1_pcs_esistream_fsm_en_i = 1'b0;
    parameter cfg_tx1_pcs_loopback_i = 1'b0;
    parameter cfg_tx1_pcs_polarity_i = 1'b0;
    parameter cfg_tx1_pcs_protocol_size_i = 1'b0;
    parameter cfg_tx1_pcs_replace_bypass_i = 1'b0;
    parameter cfg_tx1_pcs_scr_bypass_i = 1'b0;
    parameter cfg_tx1_pcs_scr_init_i = 17'b00000000000000000;
    parameter cfg_tx1_pcs_sync_supported_i = 1'b0;
    parameter cfg_tx1_pma_clk_pos_i = 1'b0;
    parameter cfg_tx1_pma_loopback_i = 1'b0;
    parameter cfg_tx2_gearbox_en_i = 1'b0;
    parameter cfg_tx2_gearbox_mode_i = 1'b0;
    parameter cfg_tx2_pcs_8b_scr_sel_i = 1'b0;
    parameter cfg_tx2_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_tx2_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_tx2_pcs_enc_bypass_i = 1'b0;
    parameter cfg_tx2_pcs_esistream_fsm_en_i = 1'b0;
    parameter cfg_tx2_pcs_loopback_i = 1'b0;
    parameter cfg_tx2_pcs_polarity_i = 1'b0;
    parameter cfg_tx2_pcs_protocol_size_i = 1'b0;
    parameter cfg_tx2_pcs_replace_bypass_i = 1'b0;
    parameter cfg_tx2_pcs_scr_bypass_i = 1'b0;
    parameter cfg_tx2_pcs_scr_init_i = 17'b00000000000000000;
    parameter cfg_tx2_pcs_sync_supported_i = 1'b0;
    parameter cfg_tx2_pma_clk_pos_i = 1'b0;
    parameter cfg_tx2_pma_loopback_i = 1'b0;
    parameter cfg_tx3_gearbox_en_i = 1'b0;
    parameter cfg_tx3_gearbox_mode_i = 1'b0;
    parameter cfg_tx3_pcs_8b_scr_sel_i = 1'b0;
    parameter cfg_tx3_pcs_bypass_pma_cdc_i = 1'b0;
    parameter cfg_tx3_pcs_bypass_usr_cdc_i = 1'b0;
    parameter cfg_tx3_pcs_enc_bypass_i = 1'b0;
    parameter cfg_tx3_pcs_esistream_fsm_en_i = 1'b0;
    parameter cfg_tx3_pcs_loopback_i = 1'b0;
    parameter cfg_tx3_pcs_polarity_i = 1'b0;
    parameter cfg_tx3_pcs_protocol_size_i = 1'b0;
    parameter cfg_tx3_pcs_replace_bypass_i = 1'b0;
    parameter cfg_tx3_pcs_scr_bypass_i = 1'b0;
    parameter cfg_tx3_pcs_scr_init_i = 17'b00000000000000000;
    parameter cfg_tx3_pcs_sync_supported_i = 1'b0;
    parameter cfg_tx3_pma_clk_pos_i = 1'b0;
    parameter cfg_tx3_pma_loopback_i = 1'b0;
    parameter location = "";
    parameter rx_usrclk_use_pcs_clk_2 = 1'b0;
    parameter tx_usrclk_use_pcs_clk_2 = 1'b0;
endmodule
