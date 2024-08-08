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
