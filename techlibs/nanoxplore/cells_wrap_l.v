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

module NX_DSP_L_SPLIT(CK, R, RZ, WE, CI, CCI, CO, CO36, CO56, OVF, CCO, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO
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
    output CO;
    output CO36;
    output CO56;
    input [55:0] CZI;
    output [55:0] CZO;
    input [17:0] D;
    output OVF;
    input R;
    input RZ;
    input WE;
    output [55:0] Z;
    parameter ALU_DYNAMIC_OP = 1'b0;
    parameter ALU_MUX = 1'b0;
    parameter ALU_OP = 6'b000000;
    parameter CO_SEL = 1'b0;
    parameter ENABLE_PR_ALU_RST = 1'b0;
    parameter ENABLE_PR_A_RST = 1'b0;
    parameter ENABLE_PR_B_RST = 1'b0;
    parameter ENABLE_PR_CI_RST = 1'b0;
    parameter ENABLE_PR_CO_RST = 1'b0;
    parameter ENABLE_PR_C_RST = 1'b0;
    parameter ENABLE_PR_D_RST = 1'b0;
    parameter ENABLE_PR_MULT_RST = 1'b0;
    parameter ENABLE_PR_OV_RST = 1'b0;
    parameter ENABLE_PR_P_RST = 1'b0;
    parameter ENABLE_PR_X_RST = 1'b0;
    parameter ENABLE_PR_Y_RST = 1'b0;
    parameter ENABLE_PR_Z_RST = 1'b0;
    parameter ENABLE_SATURATION = 1'b0;
    parameter MUX_A = 1'b0;
    parameter MUX_B = 1'b0;
    parameter MUX_CI = 1'b0;
    parameter MUX_P = 1'b0;
    parameter MUX_X = 2'b00;
    parameter MUX_Y = 1'b0;
    parameter MUX_Z = 1'b0;
    parameter PRE_ADDER_OP = 1'b0;
    parameter PR_ALU_MUX = 1'b0;
    parameter PR_A_CASCADE_MUX = 2'b00;
    parameter PR_A_MUX = 2'b00;
    parameter PR_B_CASCADE_MUX = 2'b00;
    parameter PR_B_MUX = 2'b00;
    parameter PR_CI_MUX = 1'b0;
    parameter PR_CO_MUX = 1'b0;
    parameter PR_C_MUX = 1'b0;
    parameter PR_D_MUX = 1'b0;
    parameter PR_MULT_MUX = 1'b0;
    parameter PR_OV_MUX = 1'b0;
    parameter PR_P_MUX = 1'b0;
    parameter PR_X_MUX = 1'b0;
    parameter PR_Y_MUX = 1'b0;
    parameter PR_Z_MUX = 1'b0;
    parameter SATURATION_RANK = 6'b000000;
    parameter SIGNED_MODE = 1'b0;
    parameter Z_FEEDBACK_SHL12 = 1'b0;

localparam RAW_CONFIG0_GEN = { CO_SEL, ALU_DYNAMIC_OP, SATURATION_RANK, ENABLE_SATURATION, Z_FEEDBACK_SHL12, MUX_Z,
       MUX_CI, MUX_Y, MUX_X, MUX_P, MUX_B, MUX_A, PRE_ADDER_OP, SIGNED_MODE };

localparam RAW_CONFIG1_GEN = { PR_OV_MUX, PR_CO_MUX, PR_Z_MUX, PR_ALU_MUX, PR_MULT_MUX, PR_Y_MUX, PR_X_MUX,
       PR_P_MUX, PR_CI_MUX, PR_D_MUX, PR_C_MUX, PR_B_CASCADE_MUX, PR_B_MUX, PR_A_CASCADE_MUX, PR_A_MUX };

localparam RAW_CONFIG2_GEN = { ENABLE_PR_OV_RST, ENABLE_PR_CO_RST, ENABLE_PR_Z_RST, ENABLE_PR_ALU_RST,
       ENABLE_PR_MULT_RST, ENABLE_PR_Y_RST, ENABLE_PR_X_RST, ENABLE_PR_P_RST, ENABLE_PR_CI_RST,
       ENABLE_PR_D_RST, ENABLE_PR_C_RST, ENABLE_PR_B_RST, ENABLE_PR_A_RST };

localparam RAW_CONFIG3_GEN = { ALU_MUX, ALU_OP };

  NX_DSP_L #(
    .std_mode(""),
    .raw_config0(RAW_CONFIG0_GEN),
    .raw_config1(RAW_CONFIG1_GEN),
    .raw_config2(RAW_CONFIG2_GEN),
    .raw_config3(RAW_CONFIG3_GEN),
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
    .CO(CO),
    .CO37(CO36),
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

module NX_DSP_L_WRAP(CCI, CCO, CI, CK, CO, CO37, CO57, OVF, R, RZ, WE, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO
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
    output CO;
    output CO37;
    output CO57;
    input [55:0] CZI;
    output [55:0] CZO;
    input [17:0] D;
    output OVF;
    input R;
    input RZ;
    input WE;
    output [55:0] Z;
    parameter raw_config0 = 20'b00000000000000000000;
    parameter raw_config1 = 19'b0000000000000000000;
    parameter raw_config2 = 13'b0000000000000;
    parameter raw_config3 = 7'b0000000;
    parameter std_mode = "";

  NX_DSP_L #(
    .std_mode(std_mode),
    .raw_config0(raw_config0),
    .raw_config1(raw_config1),
    .raw_config2(raw_config2),
    .raw_config3(raw_config3),
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
    .CO(CO),
    .CO37(CO37),
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

module NX_RFB_L_WRAP(RCK, WCK, COR, ERR, RE, WE, I, O, RA, WA);
    output COR;
    output ERR;
    input [15:0] I;
    output [15:0] O;
    input [5:0] RA;
    input RCK;
    input RE;
    input [5:0] WA;
    input WCK;
    input WE;
    parameter mem_ctxt = "";
    parameter mode = 0;
    parameter rck_edge = 1'b0;
    parameter wck_edge = 1'b0;

  NX_RFB_L #(
    .mode(mode),
    .rck_edge(rck_edge),
    .wck_edge(wck_edge),
    .mem_ctxt(mem_ctxt)
  ) _TECHMAP_REPLACE_ (
    .RCK(RCK),
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
    .COR(COR),
    .ERR(ERR),
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
    .RA1(RA[0]),
    .RA2(RA[1]),
    .RA3(RA[2]),
    .RA4(RA[3]),
    .RA5(RA[4]),
    .RA6(RA[5]),
    .RE(RE),
    .WA1(WA[0]),
    .WA2(WA[1]),
    .WA3(WA[2]),
    .WA4(WA[3]),
    .WA5(WA[4]),
    .WA6(WA[5]),
    .WE(WE)
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

  NX_RFB_L #(
    .mode(0),
    .mem_ctxt(mem_ctxt),
    .rck_edge(rck_edge),
    .wck_edge(wck_edge)
  ) _TECHMAP_REPLACE_ (
    .RCK(RCK),
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
    .COR(COR),
    .ERR(ERR),
    .O1(O1),
    .O2(O2),
    .O3(O3),
    .O4(O4),
    .O5(O5),
    .O6(O6),
    .O7(O7),
    .O8(O8),
    .O9(O9),
    .O10(O10),
    .O11(O11),
    .O12(O12),
    .O13(O13),
    .O14(O14),
    .O15(O15),
    .O16(O16),
    .RA1(RA1),
    .RA2(RA2),
    .RA3(RA3),
    .RA4(RA4),
    .RA5(RA5),
    .RA6(RA6),
    .RE(RE),
    .WA1(WA1),
    .WA2(WA2),
    .WA3(WA3),
    .WA4(WA4),
    .WA5(WA5),
    .WA6(WA6),
    .WE(WE)
  );
endmodule

//TODO
module SMUL24x32_2DSP_ACC_2DSP_L(clk, rst, we, A, B, Z);
    input [23:0] A;
    input [31:0] B;
    output [91:0] Z;
    input clk;
    input rst;
    input we;
endmodule

//TODO
module NX_HSSL_L_FULL(hssl_clk_user_i, hssl_clk_ref_i, hssl_clock_o, usr_com_tx_pma_pre_sign_i, usr_com_tx_pma_pre_en_i, usr_com_tx_pma_main_sign_i, usr_com_rx_pma_m_eye_i, usr_com_tx_pma_post_sign_i, usr_pll_pma_rst_n_i, usr_main_rst_n_i, usr_calibrate_pma_en_i, usr_pcs_ctrl_pll_lock_en_i, usr_pcs_ctrl_ovs_en_i, usr_pll_lock_o, usr_calibrate_pma_out_o, pma_clk_ext_i, usr_tx0_ctrl_replace_en_i, usr_tx0_rst_n_i, usr_tx0_pma_clk_en_i, usr_tx0_busy_o, pma_tx0_o
, usr_rx0_ctrl_dscr_en_i, usr_rx0_ctrl_dec_en_i, usr_rx0_ctrl_align_en_i, usr_rx0_ctrl_align_sync_i, usr_rx0_ctrl_replace_en_i, usr_rx0_ctrl_el_buff_rst_i, usr_rx0_ctrl_el_buff_fifo_en_i, usr_rx0_rst_n_i, usr_rx0_pma_cdr_rst_i, usr_rx0_pma_ckgen_rst_n_i, usr_rx0_pma_pll_rst_n_i, usr_rx0_pma_loss_of_signal_o, usr_rx0_ctrl_char_is_aligned_o, usr_rx0_busy_o, usr_rx0_pll_lock_o, pma_rx0_i, usr_tx1_ctrl_replace_en_i, usr_tx1_rst_n_i, usr_tx1_pma_clk_en_i, usr_tx1_busy_o, pma_tx1_o
, usr_rx1_ctrl_dscr_en_i, usr_rx1_ctrl_dec_en_i, usr_rx1_ctrl_align_en_i, usr_rx1_ctrl_align_sync_i, usr_rx1_ctrl_replace_en_i, usr_rx1_ctrl_el_buff_rst_i, usr_rx1_ctrl_el_buff_fifo_en_i, usr_rx1_rst_n_i, usr_rx1_pma_cdr_rst_i, usr_rx1_pma_ckgen_rst_n_i, usr_rx1_pma_pll_rst_n_i, usr_rx1_pma_loss_of_signal_o, usr_rx1_ctrl_char_is_aligned_o, usr_rx1_busy_o, usr_rx1_pll_lock_o, pma_rx1_i, usr_tx2_ctrl_replace_en_i, usr_tx2_rst_n_i, usr_tx2_pma_clk_en_i, usr_tx2_busy_o, pma_tx2_o
, usr_rx2_ctrl_dscr_en_i, usr_rx2_ctrl_dec_en_i, usr_rx2_ctrl_align_en_i, usr_rx2_ctrl_align_sync_i, usr_rx2_ctrl_replace_en_i, usr_rx2_ctrl_el_buff_rst_i, usr_rx2_ctrl_el_buff_fifo_en_i, usr_rx2_rst_n_i, usr_rx2_pma_cdr_rst_i, usr_rx2_pma_ckgen_rst_n_i, usr_rx2_pma_pll_rst_n_i, usr_rx2_pma_loss_of_signal_o, usr_rx2_ctrl_char_is_aligned_o, usr_rx2_busy_o, usr_rx2_pll_lock_o, pma_rx2_i, usr_tx3_ctrl_replace_en_i, usr_tx3_rst_n_i, usr_tx3_pma_clk_en_i, usr_tx3_busy_o, pma_tx3_o
, usr_rx3_ctrl_dscr_en_i, usr_rx3_ctrl_dec_en_i, usr_rx3_ctrl_align_en_i, usr_rx3_ctrl_align_sync_i, usr_rx3_ctrl_replace_en_i, usr_rx3_ctrl_el_buff_rst_i, usr_rx3_ctrl_el_buff_fifo_en_i, usr_rx3_rst_n_i, usr_rx3_pma_cdr_rst_i, usr_rx3_pma_ckgen_rst_n_i, usr_rx3_pma_pll_rst_n_i, usr_rx3_pma_loss_of_signal_o, usr_rx3_ctrl_char_is_aligned_o, usr_rx3_busy_o, usr_rx3_pll_lock_o, pma_rx3_i, usr_tx4_ctrl_replace_en_i, usr_tx4_rst_n_i, usr_tx4_pma_clk_en_i, usr_tx4_busy_o, pma_tx4_o
, usr_rx4_ctrl_dscr_en_i, usr_rx4_ctrl_dec_en_i, usr_rx4_ctrl_align_en_i, usr_rx4_ctrl_align_sync_i, usr_rx4_ctrl_replace_en_i, usr_rx4_ctrl_el_buff_rst_i, usr_rx4_ctrl_el_buff_fifo_en_i, usr_rx4_rst_n_i, usr_rx4_pma_cdr_rst_i, usr_rx4_pma_ckgen_rst_n_i, usr_rx4_pma_pll_rst_n_i, usr_rx4_pma_loss_of_signal_o, usr_rx4_ctrl_char_is_aligned_o, usr_rx4_busy_o, usr_rx4_pll_lock_o, pma_rx4_i, usr_tx5_ctrl_replace_en_i, usr_tx5_rst_n_i, usr_tx5_pma_clk_en_i, usr_tx5_busy_o, pma_tx5_o
, usr_rx5_ctrl_dscr_en_i, usr_rx5_ctrl_dec_en_i, usr_rx5_ctrl_align_en_i, usr_rx5_ctrl_align_sync_i, usr_rx5_ctrl_replace_en_i, usr_rx5_ctrl_el_buff_rst_i, usr_rx5_ctrl_el_buff_fifo_en_i, usr_rx5_rst_n_i, usr_rx5_pma_cdr_rst_i, usr_rx5_pma_ckgen_rst_n_i, usr_rx5_pma_pll_rst_n_i, usr_rx5_pma_loss_of_signal_o, usr_rx5_ctrl_char_is_aligned_o, usr_rx5_busy_o, usr_rx5_pll_lock_o, pma_rx5_i, usr_com_tx_pma_main_en_i, usr_com_tx_pma_margin_sel_i, usr_com_tx_pma_margin_input_sel_i, usr_com_tx_pma_margin_sel_var_i, usr_com_tx_pma_margin_input_sel_var_i
, usr_com_tx_pma_post_en_i, usr_com_tx_pma_post_input_sel_i, usr_com_tx_pma_post_input_sel_var_i, usr_com_rx_pma_ctle_cap_i, usr_com_rx_pma_ctle_resp_i, usr_com_rx_pma_ctle_resn_i, usr_com_ctrl_tx_sel_i, usr_com_ctrl_rx_sel_i, usr_calibrate_pma_res_p1_i, usr_calibrate_pma_res_n2_i, usr_calibrate_pma_res_n3_i, usr_calibrate_pma_res_p4_i, usr_calibrate_pma_sel_i, usr_main_test_i, usr_main_test_o, usr_tx0_ctrl_enc_en_i, usr_tx0_ctrl_char_is_k_i, usr_tx0_ctrl_scr_en_i, usr_tx0_ctrl_end_of_multiframe_i, usr_tx0_ctrl_end_of_frame_i, usr_tx0_test_i
, usr_tx0_data_i, usr_tx0_test_o, usr_rx0_data_o, usr_rx0_ctrl_ovs_bit_sel_i, usr_rx0_test_i, usr_rx0_ctrl_char_is_comma_o, usr_rx0_ctrl_char_is_k_o, usr_rx0_ctrl_not_in_table_o, usr_rx0_ctrl_disp_err_o, usr_rx0_ctrl_char_is_a_o, usr_rx0_ctrl_char_is_f_o, usr_rx0_test_o, usr_tx1_ctrl_enc_en_i, usr_tx1_ctrl_char_is_k_i, usr_tx1_ctrl_scr_en_i, usr_tx1_ctrl_end_of_multiframe_i, usr_tx1_ctrl_end_of_frame_i, usr_tx1_test_i, usr_tx1_data_i, usr_tx1_test_o, usr_rx1_data_o
, usr_rx1_ctrl_ovs_bit_sel_i, usr_rx1_test_i, usr_rx1_ctrl_char_is_comma_o, usr_rx1_ctrl_char_is_k_o, usr_rx1_ctrl_not_in_table_o, usr_rx1_ctrl_disp_err_o, usr_rx1_ctrl_char_is_a_o, usr_rx1_ctrl_char_is_f_o, usr_rx1_test_o, usr_tx2_ctrl_enc_en_i, usr_tx2_ctrl_char_is_k_i, usr_tx2_ctrl_scr_en_i, usr_tx2_ctrl_end_of_multiframe_i, usr_tx2_ctrl_end_of_frame_i, usr_tx2_test_i, usr_tx2_data_i, usr_tx2_test_o, usr_rx2_data_o, usr_rx2_ctrl_ovs_bit_sel_i, usr_rx2_test_i, usr_rx2_ctrl_char_is_comma_o
, usr_rx2_ctrl_char_is_k_o, usr_rx2_ctrl_not_in_table_o, usr_rx2_ctrl_disp_err_o, usr_rx2_ctrl_char_is_a_o, usr_rx2_ctrl_char_is_f_o, usr_rx2_test_o, usr_tx3_ctrl_enc_en_i, usr_tx3_ctrl_char_is_k_i, usr_tx3_ctrl_scr_en_i, usr_tx3_ctrl_end_of_multiframe_i, usr_tx3_ctrl_end_of_frame_i, usr_tx3_test_i, usr_tx3_data_i, usr_tx3_test_o, usr_rx3_data_o, usr_rx3_ctrl_ovs_bit_sel_i, usr_rx3_test_i, usr_rx3_ctrl_char_is_comma_o, usr_rx3_ctrl_char_is_k_o, usr_rx3_ctrl_not_in_table_o, usr_rx3_ctrl_disp_err_o
, usr_rx3_ctrl_char_is_a_o, usr_rx3_ctrl_char_is_f_o, usr_rx3_test_o, usr_tx4_ctrl_enc_en_i, usr_tx4_ctrl_char_is_k_i, usr_tx4_ctrl_scr_en_i, usr_tx4_ctrl_end_of_multiframe_i, usr_tx4_ctrl_end_of_frame_i, usr_tx4_test_i, usr_tx4_data_i, usr_tx4_test_o, usr_rx4_data_o, usr_rx4_ctrl_ovs_bit_sel_i, usr_rx4_test_i, usr_rx4_ctrl_char_is_comma_o, usr_rx4_ctrl_char_is_k_o, usr_rx4_ctrl_not_in_table_o, usr_rx4_ctrl_disp_err_o, usr_rx4_ctrl_char_is_a_o, usr_rx4_ctrl_char_is_f_o, usr_rx4_test_o
, usr_tx5_ctrl_enc_en_i, usr_tx5_ctrl_char_is_k_i, usr_tx5_ctrl_scr_en_i, usr_tx5_ctrl_end_of_multiframe_i, usr_tx5_ctrl_end_of_frame_i, usr_tx5_test_i, usr_tx5_data_i, usr_tx5_test_o, usr_rx5_data_o, usr_rx5_ctrl_ovs_bit_sel_i, usr_rx5_test_i, usr_rx5_ctrl_char_is_comma_o, usr_rx5_ctrl_char_is_k_o, usr_rx5_ctrl_not_in_table_o, usr_rx5_ctrl_disp_err_o, usr_rx5_ctrl_char_is_a_o, usr_rx5_ctrl_char_is_f_o, usr_rx5_test_o, usr_com_tx_pma_pre_input_sel_i);
    input hssl_clk_ref_i;
    input hssl_clk_user_i;
    output hssl_clock_o;
    input pma_clk_ext_i;
    input pma_rx0_i;
    input pma_rx1_i;
    input pma_rx2_i;
    input pma_rx3_i;
    input pma_rx4_i;
    input pma_rx5_i;
    output pma_tx0_o;
    output pma_tx1_o;
    output pma_tx2_o;
    output pma_tx3_o;
    output pma_tx4_o;
    output pma_tx5_o;
    input usr_calibrate_pma_en_i;
    output usr_calibrate_pma_out_o;
    input [7:0] usr_calibrate_pma_res_n2_i;
    input [7:0] usr_calibrate_pma_res_n3_i;
    input [7:0] usr_calibrate_pma_res_p1_i;
    input [7:0] usr_calibrate_pma_res_p4_i;
    input [3:0] usr_calibrate_pma_sel_i;
    input [5:0] usr_com_ctrl_rx_sel_i;
    input [5:0] usr_com_ctrl_tx_sel_i;
    input [3:0] usr_com_rx_pma_ctle_cap_i;
    input [3:0] usr_com_rx_pma_ctle_resn_i;
    input [3:0] usr_com_rx_pma_ctle_resp_i;
    input usr_com_rx_pma_m_eye_i;
    input [5:0] usr_com_tx_pma_main_en_i;
    input usr_com_tx_pma_main_sign_i;
    input [3:0] usr_com_tx_pma_margin_input_sel_i;
    input [4:0] usr_com_tx_pma_margin_input_sel_var_i;
    input [3:0] usr_com_tx_pma_margin_sel_i;
    input [4:0] usr_com_tx_pma_margin_sel_var_i;
    input [4:0] usr_com_tx_pma_post_en_i;
    input [3:0] usr_com_tx_pma_post_input_sel_i;
    input [3:0] usr_com_tx_pma_post_input_sel_var_i;
    input usr_com_tx_pma_post_sign_i;
    input usr_com_tx_pma_pre_en_i;
    input [3:0] usr_com_tx_pma_pre_input_sel_i;
    input usr_com_tx_pma_pre_sign_i;
    input usr_main_rst_n_i;
    input [7:0] usr_main_test_i;
    output [7:0] usr_main_test_o;
    input usr_pcs_ctrl_ovs_en_i;
    input usr_pcs_ctrl_pll_lock_en_i;
    output usr_pll_lock_o;
    input usr_pll_pma_rst_n_i;
    output usr_rx0_busy_o;
    input usr_rx0_ctrl_align_en_i;
    input usr_rx0_ctrl_align_sync_i;
    output [7:0] usr_rx0_ctrl_char_is_a_o;
    output usr_rx0_ctrl_char_is_aligned_o;
    output [7:0] usr_rx0_ctrl_char_is_comma_o;
    output [7:0] usr_rx0_ctrl_char_is_f_o;
    output [7:0] usr_rx0_ctrl_char_is_k_o;
    input usr_rx0_ctrl_dec_en_i;
    output [7:0] usr_rx0_ctrl_disp_err_o;
    input usr_rx0_ctrl_dscr_en_i;
    input usr_rx0_ctrl_el_buff_fifo_en_i;
    input usr_rx0_ctrl_el_buff_rst_i;
    output [7:0] usr_rx0_ctrl_not_in_table_o;
    input [1:0] usr_rx0_ctrl_ovs_bit_sel_i;
    input usr_rx0_ctrl_replace_en_i;
    output [63:0] usr_rx0_data_o;
    output usr_rx0_pll_lock_o;
    input usr_rx0_pma_cdr_rst_i;
    input usr_rx0_pma_ckgen_rst_n_i;
    output usr_rx0_pma_loss_of_signal_o;
    input usr_rx0_pma_pll_rst_n_i;
    input usr_rx0_rst_n_i;
    input [3:0] usr_rx0_test_i;
    output [7:0] usr_rx0_test_o;
    output usr_rx1_busy_o;
    input usr_rx1_ctrl_align_en_i;
    input usr_rx1_ctrl_align_sync_i;
    output [7:0] usr_rx1_ctrl_char_is_a_o;
    output usr_rx1_ctrl_char_is_aligned_o;
    output [7:0] usr_rx1_ctrl_char_is_comma_o;
    output [7:0] usr_rx1_ctrl_char_is_f_o;
    output [7:0] usr_rx1_ctrl_char_is_k_o;
    input usr_rx1_ctrl_dec_en_i;
    output [7:0] usr_rx1_ctrl_disp_err_o;
    input usr_rx1_ctrl_dscr_en_i;
    input usr_rx1_ctrl_el_buff_fifo_en_i;
    input usr_rx1_ctrl_el_buff_rst_i;
    output [7:0] usr_rx1_ctrl_not_in_table_o;
    input [1:0] usr_rx1_ctrl_ovs_bit_sel_i;
    input usr_rx1_ctrl_replace_en_i;
    output [63:0] usr_rx1_data_o;
    output usr_rx1_pll_lock_o;
    input usr_rx1_pma_cdr_rst_i;
    input usr_rx1_pma_ckgen_rst_n_i;
    output usr_rx1_pma_loss_of_signal_o;
    input usr_rx1_pma_pll_rst_n_i;
    input usr_rx1_rst_n_i;
    input [3:0] usr_rx1_test_i;
    output [7:0] usr_rx1_test_o;
    output usr_rx2_busy_o;
    input usr_rx2_ctrl_align_en_i;
    input usr_rx2_ctrl_align_sync_i;
    output [7:0] usr_rx2_ctrl_char_is_a_o;
    output usr_rx2_ctrl_char_is_aligned_o;
    output [7:0] usr_rx2_ctrl_char_is_comma_o;
    output [7:0] usr_rx2_ctrl_char_is_f_o;
    output [7:0] usr_rx2_ctrl_char_is_k_o;
    input usr_rx2_ctrl_dec_en_i;
    output [7:0] usr_rx2_ctrl_disp_err_o;
    input usr_rx2_ctrl_dscr_en_i;
    input usr_rx2_ctrl_el_buff_fifo_en_i;
    input usr_rx2_ctrl_el_buff_rst_i;
    output [7:0] usr_rx2_ctrl_not_in_table_o;
    input [1:0] usr_rx2_ctrl_ovs_bit_sel_i;
    input usr_rx2_ctrl_replace_en_i;
    output [63:0] usr_rx2_data_o;
    output usr_rx2_pll_lock_o;
    input usr_rx2_pma_cdr_rst_i;
    input usr_rx2_pma_ckgen_rst_n_i;
    output usr_rx2_pma_loss_of_signal_o;
    input usr_rx2_pma_pll_rst_n_i;
    input usr_rx2_rst_n_i;
    input [3:0] usr_rx2_test_i;
    output [7:0] usr_rx2_test_o;
    output usr_rx3_busy_o;
    input usr_rx3_ctrl_align_en_i;
    input usr_rx3_ctrl_align_sync_i;
    output [7:0] usr_rx3_ctrl_char_is_a_o;
    output usr_rx3_ctrl_char_is_aligned_o;
    output [7:0] usr_rx3_ctrl_char_is_comma_o;
    output [7:0] usr_rx3_ctrl_char_is_f_o;
    output [7:0] usr_rx3_ctrl_char_is_k_o;
    input usr_rx3_ctrl_dec_en_i;
    output [7:0] usr_rx3_ctrl_disp_err_o;
    input usr_rx3_ctrl_dscr_en_i;
    input usr_rx3_ctrl_el_buff_fifo_en_i;
    input usr_rx3_ctrl_el_buff_rst_i;
    output [7:0] usr_rx3_ctrl_not_in_table_o;
    input [1:0] usr_rx3_ctrl_ovs_bit_sel_i;
    input usr_rx3_ctrl_replace_en_i;
    output [63:0] usr_rx3_data_o;
    output usr_rx3_pll_lock_o;
    input usr_rx3_pma_cdr_rst_i;
    input usr_rx3_pma_ckgen_rst_n_i;
    output usr_rx3_pma_loss_of_signal_o;
    input usr_rx3_pma_pll_rst_n_i;
    input usr_rx3_rst_n_i;
    input [3:0] usr_rx3_test_i;
    output [7:0] usr_rx3_test_o;
    output usr_rx4_busy_o;
    input usr_rx4_ctrl_align_en_i;
    input usr_rx4_ctrl_align_sync_i;
    output [7:0] usr_rx4_ctrl_char_is_a_o;
    output usr_rx4_ctrl_char_is_aligned_o;
    output [7:0] usr_rx4_ctrl_char_is_comma_o;
    output [7:0] usr_rx4_ctrl_char_is_f_o;
    output [7:0] usr_rx4_ctrl_char_is_k_o;
    input usr_rx4_ctrl_dec_en_i;
    output [7:0] usr_rx4_ctrl_disp_err_o;
    input usr_rx4_ctrl_dscr_en_i;
    input usr_rx4_ctrl_el_buff_fifo_en_i;
    input usr_rx4_ctrl_el_buff_rst_i;
    output [7:0] usr_rx4_ctrl_not_in_table_o;
    input [1:0] usr_rx4_ctrl_ovs_bit_sel_i;
    input usr_rx4_ctrl_replace_en_i;
    output [63:0] usr_rx4_data_o;
    output usr_rx4_pll_lock_o;
    input usr_rx4_pma_cdr_rst_i;
    input usr_rx4_pma_ckgen_rst_n_i;
    output usr_rx4_pma_loss_of_signal_o;
    input usr_rx4_pma_pll_rst_n_i;
    input usr_rx4_rst_n_i;
    input [3:0] usr_rx4_test_i;
    output [7:0] usr_rx4_test_o;
    output usr_rx5_busy_o;
    input usr_rx5_ctrl_align_en_i;
    input usr_rx5_ctrl_align_sync_i;
    output [7:0] usr_rx5_ctrl_char_is_a_o;
    output usr_rx5_ctrl_char_is_aligned_o;
    output [7:0] usr_rx5_ctrl_char_is_comma_o;
    output [7:0] usr_rx5_ctrl_char_is_f_o;
    output [7:0] usr_rx5_ctrl_char_is_k_o;
    input usr_rx5_ctrl_dec_en_i;
    output [7:0] usr_rx5_ctrl_disp_err_o;
    input usr_rx5_ctrl_dscr_en_i;
    input usr_rx5_ctrl_el_buff_fifo_en_i;
    input usr_rx5_ctrl_el_buff_rst_i;
    output [7:0] usr_rx5_ctrl_not_in_table_o;
    input [1:0] usr_rx5_ctrl_ovs_bit_sel_i;
    input usr_rx5_ctrl_replace_en_i;
    output [63:0] usr_rx5_data_o;
    output usr_rx5_pll_lock_o;
    input usr_rx5_pma_cdr_rst_i;
    input usr_rx5_pma_ckgen_rst_n_i;
    output usr_rx5_pma_loss_of_signal_o;
    input usr_rx5_pma_pll_rst_n_i;
    input usr_rx5_rst_n_i;
    input [3:0] usr_rx5_test_i;
    output [7:0] usr_rx5_test_o;
    output usr_tx0_busy_o;
    input [7:0] usr_tx0_ctrl_char_is_k_i;
    input [7:0] usr_tx0_ctrl_enc_en_i;
    input [7:0] usr_tx0_ctrl_end_of_frame_i;
    input [7:0] usr_tx0_ctrl_end_of_multiframe_i;
    input usr_tx0_ctrl_replace_en_i;
    input [7:0] usr_tx0_ctrl_scr_en_i;
    input [63:0] usr_tx0_data_i;
    input usr_tx0_pma_clk_en_i;
    input usr_tx0_rst_n_i;
    input [3:0] usr_tx0_test_i;
    output [3:0] usr_tx0_test_o;
    output usr_tx1_busy_o;
    input [7:0] usr_tx1_ctrl_char_is_k_i;
    input [7:0] usr_tx1_ctrl_enc_en_i;
    input [7:0] usr_tx1_ctrl_end_of_frame_i;
    input [7:0] usr_tx1_ctrl_end_of_multiframe_i;
    input usr_tx1_ctrl_replace_en_i;
    input [7:0] usr_tx1_ctrl_scr_en_i;
    input [63:0] usr_tx1_data_i;
    input usr_tx1_pma_clk_en_i;
    input usr_tx1_rst_n_i;
    input [3:0] usr_tx1_test_i;
    output [3:0] usr_tx1_test_o;
    output usr_tx2_busy_o;
    input [7:0] usr_tx2_ctrl_char_is_k_i;
    input [7:0] usr_tx2_ctrl_enc_en_i;
    input [7:0] usr_tx2_ctrl_end_of_frame_i;
    input [7:0] usr_tx2_ctrl_end_of_multiframe_i;
    input usr_tx2_ctrl_replace_en_i;
    input [7:0] usr_tx2_ctrl_scr_en_i;
    input [63:0] usr_tx2_data_i;
    input usr_tx2_pma_clk_en_i;
    input usr_tx2_rst_n_i;
    input [3:0] usr_tx2_test_i;
    output [3:0] usr_tx2_test_o;
    output usr_tx3_busy_o;
    input [7:0] usr_tx3_ctrl_char_is_k_i;
    input [7:0] usr_tx3_ctrl_enc_en_i;
    input [7:0] usr_tx3_ctrl_end_of_frame_i;
    input [7:0] usr_tx3_ctrl_end_of_multiframe_i;
    input usr_tx3_ctrl_replace_en_i;
    input [7:0] usr_tx3_ctrl_scr_en_i;
    input [63:0] usr_tx3_data_i;
    input usr_tx3_pma_clk_en_i;
    input usr_tx3_rst_n_i;
    input [3:0] usr_tx3_test_i;
    output [3:0] usr_tx3_test_o;
    output usr_tx4_busy_o;
    input [7:0] usr_tx4_ctrl_char_is_k_i;
    input [7:0] usr_tx4_ctrl_enc_en_i;
    input [7:0] usr_tx4_ctrl_end_of_frame_i;
    input [7:0] usr_tx4_ctrl_end_of_multiframe_i;
    input usr_tx4_ctrl_replace_en_i;
    input [7:0] usr_tx4_ctrl_scr_en_i;
    input [63:0] usr_tx4_data_i;
    input usr_tx4_pma_clk_en_i;
    input usr_tx4_rst_n_i;
    input [3:0] usr_tx4_test_i;
    output [3:0] usr_tx4_test_o;
    output usr_tx5_busy_o;
    input [7:0] usr_tx5_ctrl_char_is_k_i;
    input [7:0] usr_tx5_ctrl_enc_en_i;
    input [7:0] usr_tx5_ctrl_end_of_frame_i;
    input [7:0] usr_tx5_ctrl_end_of_multiframe_i;
    input usr_tx5_ctrl_replace_en_i;
    input [7:0] usr_tx5_ctrl_scr_en_i;
    input [63:0] usr_tx5_data_i;
    input usr_tx5_pma_clk_en_i;
    input usr_tx5_rst_n_i;
    input [3:0] usr_tx5_test_i;
    output [3:0] usr_tx5_test_o;
    parameter cfg_main_i = 34'b0000000000000000000000000000000000;
    parameter cfg_rx0_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_rx1_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_rx2_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_rx3_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_rx4_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_rx5_i = 160'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
    parameter cfg_tx0_i = 0;
    parameter cfg_tx1_i = 0;
    parameter cfg_tx2_i = 0;
    parameter cfg_tx3_i = 0;
    parameter cfg_tx4_i = 0;
    parameter cfg_tx5_i = 0;
    parameter location = "";
endmodule
