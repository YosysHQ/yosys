//(* blackbox *)
//module NX_LUT(I1, I2, I3, I4, O);
//    input I1;
//    input I2;
//    input I3;
//    input I4;
//    output O;
//    parameter lut_table = 16'b0000000000000000;
//endmodule

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

// Bypass mode of NX_GCK_U
//(* blackbox *)
//module NX_BD(I, O);
//    input I;
//    output O;
//    parameter mode = "global_lowskew";
//endmodule

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

// Special mode of NX_DFF
//(* blackbox *)
//module NX_BFF(I, O);
//    input I;
//    output O;
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

// Special mode of NX_DFR
//(* blackbox *)
//module NX_BFR(I, O);
//    input I;
//    output O;
//    parameter data_inv = 1'b0;
//    parameter iobname = "";
//    parameter location = "";
//    parameter mode = 0;
//    parameter path = 0;
//    parameter ring = 0;
//endmodule

// NX_RAM related
(* blackbox *)
module NX_ECC(CKD, CHK, COR, ERR);
    input CHK;
    input CKD;
    output COR;
    output ERR;
endmodule

//TODO
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

//TODO
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

//TODO
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

//TODO
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
