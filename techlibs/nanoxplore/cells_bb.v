(* blackbox *)
module NX_BD(I, O);
    input I;
    output O;
    parameter mode = "global_lowskew";
endmodule

(* blackbox *)
module NX_BFF(I, O);
    input I;
    output O;
endmodule

(* blackbox *)
module NX_BFR(I, O);
    input I;
    output O;
    parameter data_inv = 1'b0;
    parameter iobname = "";
    parameter location = "";
    parameter mode = 0;
    parameter path = 0;
    parameter ring = 0;
endmodule

//(* blackbox *)
//module NX_CY(A1, A2, A3, A4, B1, B2, B3, B4, CI, CO, S1, S2, S3, S4);
//    input A1;
//    input A2;
//    input A3;
//    input A4;
//    input B1;
//    input B2;
//    input B3;
//    input B4;
//    input CI;
//    output CO;
//    output S1;
//    output S2;
//    output S3;
//    output S4;
//    parameter add_carry = 0;
//endmodule

(* blackbox *)
module NX_DES(FCK, SCK, R, IO, DCK, DRL, DIG, FZ, FLD, FLG, O, DS, DRA, DRI, DRO, DID);
    input DCK;
    output [5:0] DID;
    input DIG;
    input [5:0] DRA;
    input [5:0] DRI;
    input DRL;
    output [5:0] DRO;
    input [1:0] DS;
    input FCK;
    output FLD;
    output FLG;
    input FZ;
    input IO;
    output [4:0] O;
    input R;
    input SCK;
    parameter data_size = 5;
    parameter differential = "";
    parameter dpath_dynamic = 1'b0;
    parameter drive = "";
    parameter inputDelayLine = "";
    parameter inputSignalSlope = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter standard = "";
    parameter termination = "";
    parameter terminationReference = "";
    parameter turbo = "";
    parameter weakTermination = "";
endmodule

//(* blackbox *)
//module NX_DFF(I, CK, L, R, O);
//    input CK;
//    input I;
//    input L;
//    output O;
//    input R;
//    parameter dff_ctxt = 1'b0;
//    parameter dff_edge = 1'b0;
//    parameter dff_init = 1'b0;
//    parameter dff_load = 1'b0;
//    parameter dff_sync = 1'b0;
//    parameter dff_type = 1'b0;
//endmodule

(* blackbox *)
module NX_DFR(I, CK, L, R, O);
    input CK;
    input I;
    input L;
    output O;
    input R;
    parameter data_inv = 1'b0;
    parameter dff_edge = 1'b0;
    parameter dff_init = 1'b0;
    parameter dff_load = 1'b0;
    parameter dff_sync = 1'b0;
    parameter dff_type = 1'b0;
    parameter iobname = "";
    parameter location = "";
    parameter mode = 0;
    parameter path = 0;
    parameter ring = 0;
endmodule

(* blackbox *)
module NX_ECC(CKD, CHK, COR, ERR);
    input CHK;
    input CKD;
    output COR;
    output ERR;
endmodule

(* blackbox *)
module NX_IOB(I, C, T, O, IO);
    input C;
    input I;
    inout IO;
    output O;
    input T;
    parameter differential = "";
    parameter drive = "";
    parameter dynDrive = "";
    parameter dynInput = "";
    parameter dynTerm = "";
    parameter extra = 3;
    parameter inputDelayLine = "";
    parameter inputDelayOn = "";
    parameter inputSignalSlope = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter outputCapacity = "";
    parameter outputDelayLine = "";
    parameter outputDelayOn = "";
    parameter slewRate = "";
    parameter standard = "";
    parameter termination = "";
    parameter terminationReference = "";
    parameter turbo = "";
    parameter weakTermination = "";
endmodule

(* blackbox *)
module NX_IOB_I(C, T, IO, O);
    input C;
    input IO;
    output O;
    input T;
    parameter differential = "";
    parameter drive = "";
    parameter dynDrive = "";
    parameter dynInput = "";
    parameter dynTerm = "";
    parameter extra = 1;
    parameter inputDelayLine = "";
    parameter inputDelayOn = "";
    parameter inputSignalSlope = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter outputCapacity = "";
    parameter outputDelayLine = "";
    parameter outputDelayOn = "";
    parameter slewRate = "";
    parameter standard = "";
    parameter termination = "";
    parameter terminationReference = "";
    parameter turbo = "";
    parameter weakTermination = "";
endmodule

(* blackbox *)
module NX_IOB_O(I, C, T, IO);
    input C;
    input I;
    output IO;
    input T;
    parameter differential = "";
    parameter drive = "";
    parameter dynDrive = "";
    parameter dynInput = "";
    parameter dynTerm = "";
    parameter extra = 2;
    parameter inputDelayLine = "";
    parameter inputDelayOn = "";
    parameter inputSignalSlope = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter outputCapacity = "";
    parameter outputDelayLine = "";
    parameter outputDelayOn = "";
    parameter slewRate = "";
    parameter standard = "";
    parameter termination = "";
    parameter terminationReference = "";
    parameter turbo = "";
    parameter weakTermination = "";
endmodule

(* blackbox *)
module NX_IOM_BIN2GRP(GS, DS, GVON, GVIN, GVDN, PA, LA);
    input [1:0] DS;
    input GS;
    output [2:0] GVDN;
    output [2:0] GVIN;
    output [2:0] GVON;
    input [5:0] LA;
    output [3:0] PA;
endmodule

//(* blackbox *)
//module NX_LUT(I1, I2, I3, I4, O);
//    input I1;
//    input I2;
//    input I3;
//    input I4;
//    output O;
//    parameter lut_table = 16'b0000000000000000;
//endmodule

(* blackbox *)
module NX_RAM(ACK, ACKC, ACKD, ACKR, BCK, BCKC, BCKD, BCKR, AI1, AI2, AI3, AI4, AI5, AI6, AI7, AI8, AI9, AI10, AI11, AI12, AI13
, AI14, AI15, AI16, AI17, AI18, AI19, AI20, AI21, AI22, AI23, AI24, BI1, BI2, BI3, BI4, BI5, BI6, BI7, BI8, BI9, BI10
, BI11, BI12, BI13, BI14, BI15, BI16, BI17, BI18, BI19, BI20, BI21, BI22, BI23, BI24, ACOR, AERR, BCOR, BERR, AO1, AO2, AO3
, AO4, AO5, AO6, AO7, AO8, AO9, AO10, AO11, AO12, AO13, AO14, AO15, AO16, AO17, AO18, AO19, AO20, AO21, AO22, AO23, AO24
, BO1, BO2, BO3, BO4, BO5, BO6, BO7, BO8, BO9, BO10, BO11, BO12, BO13, BO14, BO15, BO16, BO17, BO18, BO19, BO20, BO21
, BO22, BO23, BO24, AA1, AA2, AA3, AA4, AA5, AA6, AA7, AA8, AA9, AA10, AA11, AA12, AA13, AA14, AA15, AA16, ACS, AWE
, AR, BA1, BA2, BA3, BA4, BA5, BA6, BA7, BA8, BA9, BA10, BA11, BA12, BA13, BA14, BA15, BA16, BCS, BWE, BR);
    input AA1;
    input AA10;
    input AA11;
    input AA12;
    input AA13;
    input AA14;
    input AA15;
    input AA16;
    input AA2;
    input AA3;
    input AA4;
    input AA5;
    input AA6;
    input AA7;
    input AA8;
    input AA9;
    input ACK;
    input ACKC;
    input ACKD;
    input ACKR;
    output ACOR;
    input ACS;
    output AERR;
    input AI1;
    input AI10;
    input AI11;
    input AI12;
    input AI13;
    input AI14;
    input AI15;
    input AI16;
    input AI17;
    input AI18;
    input AI19;
    input AI2;
    input AI20;
    input AI21;
    input AI22;
    input AI23;
    input AI24;
    input AI3;
    input AI4;
    input AI5;
    input AI6;
    input AI7;
    input AI8;
    input AI9;
    output AO1;
    output AO10;
    output AO11;
    output AO12;
    output AO13;
    output AO14;
    output AO15;
    output AO16;
    output AO17;
    output AO18;
    output AO19;
    output AO2;
    output AO20;
    output AO21;
    output AO22;
    output AO23;
    output AO24;
    output AO3;
    output AO4;
    output AO5;
    output AO6;
    output AO7;
    output AO8;
    output AO9;
    input AR;
    input AWE;
    input BA1;
    input BA10;
    input BA11;
    input BA12;
    input BA13;
    input BA14;
    input BA15;
    input BA16;
    input BA2;
    input BA3;
    input BA4;
    input BA5;
    input BA6;
    input BA7;
    input BA8;
    input BA9;
    input BCK;
    input BCKC;
    input BCKD;
    input BCKR;
    output BCOR;
    input BCS;
    output BERR;
    input BI1;
    input BI10;
    input BI11;
    input BI12;
    input BI13;
    input BI14;
    input BI15;
    input BI16;
    input BI17;
    input BI18;
    input BI19;
    input BI2;
    input BI20;
    input BI21;
    input BI22;
    input BI23;
    input BI24;
    input BI3;
    input BI4;
    input BI5;
    input BI6;
    input BI7;
    input BI8;
    input BI9;
    output BO1;
    output BO10;
    output BO11;
    output BO12;
    output BO13;
    output BO14;
    output BO15;
    output BO16;
    output BO17;
    output BO18;
    output BO19;
    output BO2;
    output BO20;
    output BO21;
    output BO22;
    output BO23;
    output BO24;
    output BO3;
    output BO4;
    output BO5;
    output BO6;
    output BO7;
    output BO8;
    output BO9;
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
    parameter raw_l_enable = 1'b0;
    parameter raw_l_extend = 4'b0000;
    parameter raw_u_enable = 1'b0;
    parameter raw_u_extend = 8'b00000000;
    parameter std_mode = "";
endmodule

(* blackbox *)
module NX_SER(FCK, SCK, R, IO, DCK, DRL, I, DS, DRA, DRI, DRO, DID);
    input DCK;
    output [5:0] DID;
    input [5:0] DRA;
    input [5:0] DRI;
    input DRL;
    output [5:0] DRO;
    input [1:0] DS;
    input FCK;
    input [4:0] I;
    output IO;
    input R;
    input SCK;
    parameter data_size = 5;
    parameter differential = "";
    parameter drive = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter outputCapacity = "";
    parameter outputDelayLine = "";
    parameter slewRate = "";
    parameter spath_dynamic = 1'b0;
    parameter standard = "";
endmodule

(* blackbox *)
module NX_SERDES(FCK, SCK, RTX, RRX, CI, CCK, CL, CR, IO, DCK, DRL, DIG, FZ, FLD, FLG, I, O, DS, DRA, DRI, DRO
, DID);
    input CCK;
    input CI;
    input CL;
    input CR;
    input DCK;
    output [5:0] DID;
    input DIG;
    input [5:0] DRA;
    input [5:0] DRI;
    input DRL;
    output [5:0] DRO;
    input [1:0] DS;
    input FCK;
    output FLD;
    output FLG;
    input FZ;
    input [4:0] I;
    inout IO;
    output [4:0] O;
    input RRX;
    input RTX;
    input SCK;
    parameter cpath_registered = 1'b0;
    parameter data_size = 5;
    parameter differential = "";
    parameter dpath_dynamic = 1'b0;
    parameter drive = "";
    parameter inputDelayLine = "";
    parameter inputSignalSlope = "";
    parameter location = "";
    parameter locked = 1'b0;
    parameter outputCapacity = "";
    parameter outputDelayLine = "";
    parameter slewRate = "";
    parameter spath_dynamic = 1'b0;
    parameter standard = "";
    parameter termination = "";
    parameter terminationReference = "";
    parameter turbo = "";
    parameter weakTermination = "";
endmodule
