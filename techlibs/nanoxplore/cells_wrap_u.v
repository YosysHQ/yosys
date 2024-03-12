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