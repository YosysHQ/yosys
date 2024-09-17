module NX_RAM_WRAP(ACK, ACKD, ACKR, BCK, BCKD, BCKR, ACOR, AERR, BCOR, BERR, ACS, AWE, AR, BCS, BWE, BR, BI, AO, BO, AI, AA
, BA);
    input [15:0] AA;
    input ACK;
    input ACKD;
    input ACKR;
    output ACOR;
    input ACS;
    output AERR;
    input [23:0] AI;
    output [23:0] AO;
    input AR;
    input AWE;
    input [15:0] BA;
    input BCK;
    input BCKD;
    input BCKR;
    output BCOR;
    input BCS;
    output BERR;
    input [23:0] BI;
    output [23:0] BO;
    input BR;
    input BWE;
    parameter mcka_edge = 1'b0;
    parameter mckb_edge = 1'b0;
    parameter mem_ctxt = "";
    parameter pcka_edge = 1'b0;
    parameter pckb_edge = 1'b0;
    parameter pipe_ia = 1'b0;
    parameter pipe_ib = 1'b0;
    parameter pipe_oa = 1'b0;
    parameter pipe_ob = 1'b0;
    parameter raw_config0 = 4'b0000;
    parameter raw_config1 = 16'b0000000000000000;
    parameter std_mode = "";

  NX_RAM #(
    .mcka_edge(mcka_edge),
    .mckb_edge(mckb_edge),
    .mem_ctxt(mem_ctxt),
    .pcka_edge(pcka_edge),
    .pckb_edge(pckb_edge),
    .pipe_ia(pipe_ia),
    .pipe_ib(pipe_ib),
    .pipe_oa(pipe_oa),
    .pipe_ob(pipe_ob),
    .raw_config0(raw_config0),
    .raw_config1(raw_config1),
    .std_mode(std_mode)
  ) ram (
    .AA1(AA[0]),
    .AA10(AA[9]),
    .AA11(AA[10]),
    .AA12(AA[11]),
    .AA13(AA[12]),
    .AA14(AA[13]),
    .AA15(AA[14]),
    .AA16(AA[15]),
    .AA2(AA[1]),
    .AA3(AA[2]),
    .AA4(AA[3]),
    .AA5(AA[4]),
    .AA6(AA[5]),
    .AA7(AA[6]),
    .AA8(AA[7]),
    .AA9(AA[8]),
    .ACK(ACK),
    .ACKC(ACK),
    .ACKD(ACKD),
    .ACKR(ACKR),
    .ACOR(ACOR),
    .ACS(ACS),
    .AERR(AERR),
    .AI1(AI[0]),
    .AI10(AI[9]),
    .AI11(AI[10]),
    .AI12(AI[11]),
    .AI13(AI[12]),
    .AI14(AI[13]),
    .AI15(AI[14]),
    .AI16(AI[15]),
    .AI17(AI[16]),
    .AI18(AI[17]),
    .AI19(AI[18]),
    .AI2(AI[1]),
    .AI20(AI[19]),
    .AI21(AI[20]),
    .AI22(AI[21]),
    .AI23(AI[22]),
    .AI24(AI[23]),
    .AI3(AI[2]),
    .AI4(AI[3]),
    .AI5(AI[4]),
    .AI6(AI[5]),
    .AI7(AI[6]),
    .AI8(AI[7]),
    .AI9(AI[8]),
    .AO1(AO[0]),
    .AO10(AO[9]),
    .AO11(AO[10]),
    .AO12(AO[11]),
    .AO13(AO[12]),
    .AO14(AO[13]),
    .AO15(AO[14]),
    .AO16(AO[15]),
    .AO17(AO[16]),
    .AO18(AO[17]),
    .AO19(AO[18]),
    .AO2(AO[1]),
    .AO20(AO[19]),
    .AO21(AO[20]),
    .AO22(AO[21]),
    .AO23(AO[22]),
    .AO24(AO[23]),
    .AO3(AO[2]),
    .AO4(AO[3]),
    .AO5(AO[4]),
    .AO6(AO[5]),
    .AO7(AO[6]),
    .AO8(AO[7]),
    .AO9(AO[8]),
    .AR(AR),
    .AWE(AWE),
    .BA1(BA[0]),
    .BA10(BA[9]),
    .BA11(BA[10]),
    .BA12(BA[11]),
    .BA13(BA[12]),
    .BA14(BA[13]),
    .BA15(BA[14]),
    .BA16(BA[15]),
    .BA2(BA[1]),
    .BA3(BA[2]),
    .BA4(BA[3]),
    .BA5(BA[4]),
    .BA6(BA[5]),
    .BA7(BA[6]),
    .BA8(BA[7]),
    .BA9(BA[8]),
    .BCK(BCK),
    .BCKC(BCK),
    .BCKD(BCKD),
    .BCKR(BCKR),
    .BCOR(BCOR),
    .BCS(BCS),
    .BERR(BERR),
    .BI1(BI[0]),
    .BI10(BI[9]),
    .BI11(BI[10]),
    .BI12(BI[11]),
    .BI13(BI[12]),
    .BI14(BI[13]),
    .BI15(BI[14]),
    .BI16(BI[15]),
    .BI17(BI[16]),
    .BI18(BI[17]),
    .BI19(BI[18]),
    .BI2(BI[1]),
    .BI20(BI[19]),
    .BI21(BI[20]),
    .BI22(BI[21]),
    .BI23(BI[22]),
    .BI24(BI[23]),
    .BI3(BI[2]),
    .BI4(BI[3]),
    .BI5(BI[4]),
    .BI6(BI[5]),
    .BI7(BI[6]),
    .BI8(BI[7]),
    .BI9(BI[8]),
    .BO1(BO[0]),
    .BO10(BO[9]),
    .BO11(BO[10]),
    .BO12(BO[11]),
    .BO13(BO[12]),
    .BO14(BO[13]),
    .BO15(BO[14]),
    .BO16(BO[15]),
    .BO17(BO[16]),
    .BO18(BO[17]),
    .BO19(BO[18]),
    .BO2(BO[1]),
    .BO20(BO[19]),
    .BO21(BO[20]),
    .BO22(BO[21]),
    .BO23(BO[22]),
    .BO24(BO[23]),
    .BO3(BO[2]),
    .BO4(BO[3]),
    .BO5(BO[4]),
    .BO6(BO[5]),
    .BO7(BO[6]),
    .BO8(BO[7]),
    .BO9(BO[8]),
    .BR(BR),
    .BWE(BWE)
  );

endmodule

