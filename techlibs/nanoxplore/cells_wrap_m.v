module NX_DSP_SPLIT(CK, R, RZ, WE, CI, CCI, CO, CO36, CO48, OVF, CCO, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO , CZO);
    input [23:0] A;
    input [17:0] B;
    input [35:0] C;
    input [17:0] CAI;
    output [17:0] CAO;
    input [17:0] CBI;
    output [17:0] CBO;
    input CCI;
    output CCO;
    input CI;
    input CK;
    output CO;
    output CO36;
    output CO48;
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

localparam RAW_CONFIG3_GEN = { ALU_MUX,  ALU_OP };

  NX_DSP #(
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
    .CO49(CO48),

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

module NX_DSP_WRAP(CCI, CCO, CI, CK, CO, CO37, CO49, OVF, R, RZ, WE, A, B, C, D, Z, CAI, CBI, CZI, CAO, CBO
, CZO);
    input [23:0] A;
    input [17:0] B;
    input [35:0] C;
    input [17:0] CAI;
    output [17:0] CAO;
    input [17:0] CBI;
    output [17:0] CBO;
    input CCI;
    output CCO;
    input CI;
    input CK;
    output CO;
    output CO37;
    output CO49;
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

  NX_DSP #(
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
    .CO49(CO49),

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

module NX_RFB_WRAP(RCK, WCK, COR, ERR, RE, WE, I, O, RA, WA);
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
    parameter rck_edge = 1'b0;
    parameter wck_edge = 1'b0;

  NX_RFB_M #(
    .mem_ctxt(mem_ctxt),
    .rck_edge(rck_edge),
    .wck_edge(wck_edge)
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

  NX_RFB_M #(
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

module NX_IOM_CONTROL(RTCK1, RRCK1, WTCK1, WRCK1, RTCK2, RRCK2, WTCK2, WRCK2, CTCK, C1TW, C1TS, C1RW1, C1RW2, C1RW3, C1RNE, C1RS, C2TW, C2TS, C2RW1, C2RW2, C2RW3
, C2RNE, C2RS, FA1, FA2, FA3, FA4, FA5, FA6, FZ, DC, CCK, DCK, DRI1, DRI2, DRI3, DRI4, DRI5, DRI6, DRA1, DRA2, DRA3
, DRA4, DRA5, DRA6, DRL, DOS, DOG, DIS, DIG, DPAS, DPAG, DQSS, DQSG, DS1, DS2, CAD1, CAD2, CAD3, CAD4, CAD5, CAD6, CAP1
, CAP2, CAP3, CAP4, CAN1, CAN2, CAN3, CAN4, CAT1, CAT2, CAT3, CAT4, SPI1, SPI2, SPI3, CKO1, CKO2, FLD, FLG, C1RED, C2RED, DRO1
, DRO2, DRO3, DRO4, DRO5, DRO6, CAL, LINK2, LINK3, LINK4, LINK5, LINK6, LINK7, LINK8, LINK9, LINK10, LINK11, LINK12, LINK13, LINK14, LINK15, LINK16
, LINK17, LINK18, LINK19, LINK20, LINK21, LINK22, LINK23, LINK24, LINK25, LINK26, LINK27, LINK28, LINK29, LINK30, LINK31, LINK32, LINK33, LINK34, LINK1);
    output C1RED;
    input C1RNE;
    input C1RS;
    input C1RW1;
    input C1RW2;
    input C1RW3;
    input C1TS;
    input C1TW;
    output C2RED;
    input C2RNE;
    input C2RS;
    input C2RW1;
    input C2RW2;
    input C2RW3;
    input C2TS;
    input C2TW;
    input CAD1;
    input CAD2;
    input CAD3;
    input CAD4;
    input CAD5;
    input CAD6;
    output CAL;
    input CAN1;
    input CAN2;
    input CAN3;
    input CAN4;
    input CAP1;
    input CAP2;
    input CAP3;
    input CAP4;
    input CAT1;
    input CAT2;
    input CAT3;
    input CAT4;
    input CCK;
    output CKO1;
    output CKO2;
    input CTCK;
    input DC;
    input DCK;
    input DIG;
    input DIS;
    input DOG;
    input DOS;
    input DPAG;
    input DPAS;
    input DQSG;
    input DQSS;
    input DRA1;
    input DRA2;
    input DRA3;
    input DRA4;
    input DRA5;
    input DRA6;
    input DRI1;
    input DRI2;
    input DRI3;
    input DRI4;
    input DRI5;
    input DRI6;
    input DRL;
    output DRO1;
    output DRO2;
    output DRO3;
    output DRO4;
    output DRO5;
    output DRO6;
    input DS1;
    input DS2;
    input FA1;
    input FA2;
    input FA3;
    input FA4;
    input FA5;
    input FA6;
    output FLD;
    output FLG;
    input FZ;
    inout [41:0] LINK1;
    inout [41:0] LINK10;
    inout [41:0] LINK11;
    inout [41:0] LINK12;
    inout [41:0] LINK13;
    inout [41:0] LINK14;
    inout [41:0] LINK15;
    inout [41:0] LINK16;
    inout [41:0] LINK17;
    inout [41:0] LINK18;
    inout [41:0] LINK19;
    inout [41:0] LINK2;
    inout [41:0] LINK20;
    inout [41:0] LINK21;
    inout [41:0] LINK22;
    inout [41:0] LINK23;
    inout [41:0] LINK24;
    inout [41:0] LINK25;
    inout [41:0] LINK26;
    inout [41:0] LINK27;
    inout [41:0] LINK28;
    inout [41:0] LINK29;
    inout [41:0] LINK3;
    inout [41:0] LINK30;
    inout [41:0] LINK31;
    inout [41:0] LINK32;
    inout [41:0] LINK33;
    inout [41:0] LINK34;
    inout [41:0] LINK4;
    inout [41:0] LINK5;
    inout [41:0] LINK6;
    inout [41:0] LINK7;
    inout [41:0] LINK8;
    inout [41:0] LINK9;
    input RRCK1;
    input RRCK2;
    input RTCK1;
    input RTCK2;
    input SPI1;
    input SPI2;
    input SPI3;
    input WRCK1;
    input WRCK2;
    input WTCK1;
    input WTCK2;
    parameter div_rx1 = 4'b0000;
    parameter div_rx2 = 4'b0000;
    parameter div_tx1 = 4'b0000;
    parameter div_tx2 = 4'b0000;
    parameter inv_di_fclk1 = 1'b0;
    parameter inv_di_fclk2 = 1'b0;
    parameter latency1 = 1'b0;
    parameter latency2 = 1'b0;
    parameter location = "";
    parameter mode_cpath = "";
    parameter mode_epath = "";
    parameter mode_io_cal = 1'b0;
    parameter mode_rpath = "";
    parameter mode_side1 = 0;
    parameter mode_side2 = 0;
    parameter mode_tpath = "";
    parameter sel_clk_out1 = 1'b0;
    parameter sel_clk_out2 = 1'b0;
    parameter sel_clkr_rx1 = 1'b0;
    parameter sel_clkr_rx2 = 1'b0;
    parameter sel_clkw_rx1 = 2'b00;
    parameter sel_clkw_rx2 = 2'b00;

  NX_IOM_CONTROL_M #(
    .div_rx1(div_rx1),
    .div_rx2(div_rx2),
    .div_tx1(div_tx1),
    .div_tx2(div_tx2),
    .inv_di_fclk1(inv_di_fclk1),
    .inv_di_fclk2(inv_di_fclk2),
    .latency1(latency1),
    .latency2(latency2),
    .location(location),
    .mode_cpath(mode_cpath),
    .mode_epath(mode_epath),
    .mode_io_cal(mode_io_cal),
    .mode_rpath(mode_rpath),
    .mode_side1(mode_side1),
    .mode_side2(mode_side2),
    .mode_tpath(mode_tpath),
    .sel_clk_out1(sel_clk_out1),
    .sel_clk_out2(sel_clk_out2),
    .sel_clkr_rx1(sel_clkr_rx1),
    .sel_clkr_rx2(sel_clkr_rx2),
    .sel_clkw_rx1(sel_clkw_rx1),
    .sel_clkw_rx2(sel_clkw_rx2)
  ) _TECHMAP_REPLACE_ (
    .C1RED(C1RED),
    .C1RNE(C1RNE),
    .C1RS(C1RS),
    .C1RW1(C1RW1),
    .C1RW2(C1RW2),
    .C1RW3(C1RW3),
    .C1TS(C1TS),
    .C1TW(C1TW),
    .C2RED(C2RED),
    .C2RNE(C2RNE),
    .C2RS(C2RS),
    .C2RW1(C2RW1),
    .C2RW2(C2RW2),
    .C2RW3(C2RW3),
    .C2TS(C2TS),
    .C2TW(C2TW),
    .CAD1(CAD1),
    .CAD2(CAD2),
    .CAD3(CAD3),
    .CAD4(CAD4),
    .CAD5(CAD5),
    .CAD6(CAD6),
    .CAL(CAL),
    .CAN1(CAN1),
    .CAN2(CAN2),
    .CAN3(CAN3),
    .CAN4(CAN4),
    .CAP1(CAP1),
    .CAP2(CAP2),
    .CAP3(CAP3),
    .CAP4(CAP4),
    .CAT1(CAT1),
    .CAT2(CAT2),
    .CAT3(CAT3),
    .CAT4(CAT4),
    .CCK(CCK),
    .CKO1(CKO1),
    .CKO2(CKO2),
    .CTCK(CTCK),
    .DC(DC),
    .DCK(DCK),
    .DIG(DIG),
    .DIS(DIS),
    .DOG(DOG),
    .DOS(DOS),
    .DPAG(DPAG),
    .DPAS(DPAS),
    .DQSG(DQSG),
    .DQSS(DQSS),
    .DRA1(DRA1),
    .DRA2(DRA2),
    .DRA3(DRA3),
    .DRA4(DRA4),
    .DRA5(DRA5),
    .DRA6(DRA6),
    .DRI1(DRI1),
    .DRI2(DRI2),
    .DRI3(DRI3),
    .DRI4(DRI4),
    .DRI5(DRI5),
    .DRI6(DRI6),
    .DRL(DRL),
    .DRO1(DRO1),
    .DRO2(DRO2),
    .DRO3(DRO3),
    .DRO4(DRO4),
    .DRO5(DRO5),
    .DRO6(DRO6),
    .DS1(DS1),
    .DS2(DS2),
    .FA1(FA1),
    .FA2(FA2),
    .FA3(FA3),
    .FA4(FA4),
    .FA5(FA5),
    .FA6(FA6),
    .FLD(FLD),
    .FLG(FLG),
    .FZ(FZ),
    .LINK1(LINK1),
    .LINK10(LINK10),
    .LINK11(LINK11),
    .LINK12(LINK12),
    .LINK13(LINK13),
    .LINK14(LINK14),
    .LINK15(LINK15),
    .LINK16(LINK16),
    .LINK17(LINK17),
    .LINK18(LINK18),
    .LINK19(LINK19),
    .LINK2(LINK2),
    .LINK20(LINK20),
    .LINK21(LINK21),
    .LINK22(LINK22),
    .LINK23(LINK23),
    .LINK24(LINK24),
    .LINK25(LINK25),
    .LINK26(LINK26),
    .LINK27(LINK27),
    .LINK28(LINK28),
    .LINK29(LINK29),
    .LINK3(LINK3),
    .LINK30(LINK30),
    .LINK31(LINK31),
    .LINK32(LINK32),
    .LINK33(LINK33),
    .LINK34(LINK34),
    .LINK4(LINK4),
    .LINK5(LINK5),
    .LINK6(LINK6),
    .LINK7(LINK7),
    .LINK8(LINK8),
    .LINK9(LINK9),
    .RRCK1(RRCK1),
    .RRCK2(RRCK2),
    .RTCK1(RTCK1),
    .RTCK2(RTCK2),
    .SPI1(SPI1),
    .SPI2(SPI2),
    .SPI3(SPI3),
    .WRCK1(WRCK1),
    .WRCK2(WRCK2),
    .WTCK1(WTCK1),
    .WTCK2(WTCK2)
  );
endmodule

module NX_IOM_DRIVER(EI1, EI2, EI3, EI4, EI5, EL, ER, CI1, CI2, CI3, CI4, CI5, CL, CR, CTI, RI, RL, RR, CO, EO, RO1
, RO2, RO3, RO4, RO5, CTO, LINK);
    input CI1;
    input CI2;
    input CI3;
    input CI4;
    input CI5;
    input CL;
    output CO;
    input CR;
    input CTI;
    output CTO;
    input EI1;
    input EI2;
    input EI3;
    input EI4;
    input EI5;
    input EL;
    output EO;
    input ER;
    inout [41:0] LINK;
    input RI;
    input RL;
    output RO1;
    output RO2;
    output RO3;
    output RO4;
    output RO5;
    input RR;
    parameter chained = 1'b0;
    parameter cpath_edge = 1'b0;
    parameter cpath_init = 1'b0;
    parameter cpath_inv = 1'b0;
    parameter cpath_load = 1'b0;
    parameter cpath_mode = 4'b0000;
    parameter cpath_sync = 1'b0;
    parameter epath_dynamic = 1'b0;
    parameter epath_edge = 1'b0;
    parameter epath_init = 1'b0;
    parameter epath_load = 1'b0;
    parameter epath_mode = 4'b0000;
    parameter epath_sync = 1'b0;
    parameter location = "";
    parameter rpath_dynamic = 1'b0;
    parameter rpath_edge = 1'b0;
    parameter rpath_init = 1'b0;
    parameter rpath_load = 1'b0;
    parameter rpath_mode = 4'b0000;
    parameter rpath_sync = 1'b0;
    parameter symbol = "";
    parameter tpath_mode = 2'b00;
    parameter variant = "";

  NX_IOM_DRIVER_M #(
    .chained(chained),
    .cpath_edge(cpath_edge),
    .cpath_init(cpath_init),
    .cpath_inv(cpath_inv),
    .cpath_load(cpath_load),
    .cpath_mode(cpath_mode),
    .cpath_sync(cpath_sync),
    .epath_dynamic(epath_dynamic),
    .epath_edge(epath_edge),
    .epath_init(epath_init),
    .epath_load(epath_load),
    .epath_mode(epath_mode),
    .epath_sync(epath_sync),
    .location(location),
    .rpath_dynamic(rpath_dynamic),
    .rpath_edge(rpath_edge),
    .rpath_init(rpath_init),
    .rpath_load(rpath_load),
    .rpath_mode(rpath_mode),
    .rpath_sync(rpath_sync),
    .symbol(symbol),
    .tpath_mode(tpath_mode),
    .variant(variant)
  ) _TECHMAP_REPLACE_ (
    .CI1(CI1),
    .CI2(CI2),
    .CI3(CI3),
    .CI4(CI4),
    .CI5(CI5),
    .CL(CL),
    .CO(CO),
    .CR(CR),
    .CTI(CTI),
    .CTO(CTO),
    .EI1(EI1),
    .EI2(EI2),
    .EI3(EI3),
    .EI4(EI4),
    .EI5(EI5),
    .EL(EL),
    .EO(EO),
    .ER(ER),
    .LINK(LINK),
    .RI(RI),
    .RL(RL),
    .RO1(RO1),
    .RO2(RO2),
    .RO3(RO3),
    .RO4(RO4),
    .RO5(RO5),
    .RR(RR)
  );
endmodule

module NX_IOM_SERDES(RTCK, WRCK, WTCK, RRCK, TRST, RRST, CTCK, DCK, DRL, DIG, FZ, FLD, FLG, DS, DRA, DRI, DRO, DID, LINKN, LINKP);
    input CTCK;
    input DCK;
    output [5:0] DID;
    input DIG;
    input [5:0] DRA;
    input [5:0] DRI;
    input DRL;
    output [5:0] DRO;
    input [1:0] DS;
    output FLD;
    output FLG;
    input FZ;
    inout [41:0] LINKN;
    inout [41:0] LINKP;
    input RRCK;
    input RRST;
    input RTCK;
    input TRST;
    input WRCK;
    input WTCK;
    parameter data_size = 5;
    parameter location = "";

  NX_IOM_SERDES_M #(
    .data_size(data_size),
    .location(location)
  ) _TECHMAP_REPLACE_ (
    .CTCK(CTCK),
    .DCK(DCK),
    .DID(DID),
    .DIG(DIG),
    .DRA(DRA),
    .DRI(DRI),
    .DRL(DRL),
    .DRO(DRO),
    .DS(DS),
    .FLD(FLD),
    .FLG(FLG),
    .FZ(FZ),
    .LINKN(LINKN),
    .LINKP(LINKP),
    .RRCK(RRCK),
    .RRST(RRST),
    .RTCK(RTCK),
    .TRST(TRST),
    .WRCK(WRCK),
    .WTCK(WTCK)
  );
endmodule
