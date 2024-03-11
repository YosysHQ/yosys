module NX_CDC_L_2DFF(CK1, CK2, ADRSTI, BDRSTI, BI, AO, BO, AI);
    input ADRSTI;
    input [5:0] AI;
    output [5:0] AO;
    input BDRSTI;
    input [5:0] BI;
    output [5:0] BO;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter gt0_bypass_reg1 = 1'b0;
    parameter gt0_bypass_reg2 = 1'b0;
    parameter gt1_bypass_reg1 = 1'b0;
    parameter gt1_bypass_reg2 = 1'b0;
    parameter use_adest_arst = 2'b00;
    parameter use_bdest_arst = 2'b00;

  NX_CDC_L #(
    .mode(0), // -- 0: 2DFF
    .ck0_edge(ck0_edge),
    .ck1_edge(ck1_edge),
    .ack_sel(ack_sel),
    .bck_sel(bck_sel),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(2'b00),
    .use_adest_arst(use_adest_arst),
    .use_bsrc_arst(2'b00),
    .use_bdest_arst(use_bdest_arst),
    .use_csrc_arst(2'b00),
    .use_cdest_arst(2'b00),
    .use_dsrc_arst(2'b00),
    .use_ddest_arst(2'b00),
    .gt0_bypass_reg1(gt0_bypass_reg1),
    .gt0_bypass_reg2(gt0_bypass_reg2),
    .gt1_bypass_reg1(gt1_bypass_reg2),
    .gt1_bypass_reg2(gt1_bypass_reg2),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
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
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0)
  );
endmodule

module NX_CDC_L_3DFF(CK1, CK2, ASRSTI, ADRSTI, BDRSTI, BSRSTI, BI, AO, BO, AI);
    input ADRSTI;
    input [5:0] AI;
    output [5:0] AO;
    input ASRSTI;
    input BDRSTI;
    input [5:0] BI;
    output [5:0] BO;
    input BSRSTI;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter gt0_bypass_reg1 = 1'b0;
    parameter gt0_bypass_reg2 = 1'b0;
    parameter gt1_bypass_reg1 = 1'b0;
    parameter gt1_bypass_reg2 = 1'b0;
    parameter use_adest_arst = 2'b00;
    parameter use_asrc_arst = 2'b00;
    parameter use_bdest_arst = 2'b00;
    parameter use_bsrc_arst = 2'b00;

  NX_CDC_L #(
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
    .use_csrc_arst(2'b00),
    .use_cdest_arst(2'b00),
    .use_dsrc_arst(2'b00),
    .use_ddest_arst(2'b00),
    .gt0_bypass_reg1(gt0_bypass_reg1),
    .gt0_bypass_reg2(gt0_bypass_reg2),
    .gt1_bypass_reg1(gt1_bypass_reg2),
    .gt1_bypass_reg2(gt1_bypass_reg2),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
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
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0)
  );
endmodule

module NX_CDC_L_FULL(CK1, CK2, ASRSTI, ADRSTI, BDRSTI, BSRSTI, BI, AO, BO, AI);
    input ADRSTI;
    input [5:0] AI;
    output [5:0] AO;
    input ASRSTI;
    input BDRSTI;
    input [5:0] BI;
    output [5:0] BO;
    input BSRSTI;
    input CK1;
    input CK2;
    parameter ack_sel = 1'b0;
    parameter bck_sel = 1'b0;
    parameter ck0_edge = 1'b0;
    parameter ck1_edge = 1'b0;
    parameter gt0_bypass_reg1 = 1'b0;
    parameter gt0_bypass_reg2 = 1'b0;
    parameter gt1_bypass_reg1 = 1'b0;
    parameter gt1_bypass_reg2 = 1'b0;
    parameter use_adest_arst = 2'b00;
    parameter use_asrc_arst = 2'b00;
    parameter use_bdest_arst = 2'b00;
    parameter use_bsrc_arst = 2'b00;

  NX_CDC_L #(
    .mode(2), // -- 2: B2G_3DFF_G2B
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
    .use_csrc_arst(2'b00),
    .use_cdest_arst(2'b00),
    .use_dsrc_arst(2'b00),
    .use_ddest_arst(2'b00),
    .gt0_bypass_reg1(gt0_bypass_reg1),
    .gt0_bypass_reg2(gt0_bypass_reg2),
    .gt1_bypass_reg1(gt1_bypass_reg2),
    .gt1_bypass_reg2(gt1_bypass_reg2),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
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
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0)
  );
endmodule

module NX_CDC_L_BIN2GRAY(CK1, CK2, BI, AO, BO, AI);
    input [5:0] AI;
    output [5:0] AO;
    input [5:0] BI;
    output [5:0] BO;
    input CK1;
    input CK2;

  NX_CDC_L #(
    .mode(3), // -- 3: bin2gray
    .ck0_edge(1'b0),
    .ck1_edge(1'b0),
    .ack_sel(1'b0),
    .bck_sel(1'b0),
    .cck_sel(1'b0),
    .dck_sel(1'b0),
    .use_asrc_arst(2'b00),
    .use_adest_arst(2'b00),
    .use_bsrc_arst(2'b00),
    .use_bdest_arst(2'b00),
    .use_csrc_arst(2'b00),
    .use_cdest_arst(2'b00),
    .use_dsrc_arst(2'b00),
    .use_ddest_arst(2'b00),
    .gt0_bypass_reg1(1'b0),
    .gt0_bypass_reg2(1'b0),
    .gt1_bypass_reg1(1'b0),
    .gt1_bypass_reg2(1'b0),
    .link_BA(1'b0),
    .link_CB(1'b0),
    .link_DC(1'b0),
  ) _TECHMAP_REPLACE_ (
    .CK1(CK1),
    .CK2(CK2),
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
    .CI1(1'b0),
    .CI2(1'b0),
    .CI3(1'b0),
    .CI4(1'b0),
    .CI5(1'b0),
    .CI6(1'b0),
    .DI1(1'b0),
    .DI2(1'b0),
    .DI3(1'b0),
    .DI4(1'b0),
    .DI5(1'b0),
    .DI6(1'b0)
  );
endmodule
