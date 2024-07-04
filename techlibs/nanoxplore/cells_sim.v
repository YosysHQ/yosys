(* abc9_lut=1 *)
module NX_LUT(input I1, I2, I3, I4, output O);

parameter lut_table = 16'h0000;

wire [7:0] s1 = I4 ? lut_table[15:8] : lut_table[7:0];
wire [3:0] s2 = I3 ? s1[7:4] : s1[3:0];
wire [1:0] s3 = I2 ? s2[3:2] : s2[1:0];
assign O = I1 ? s3[1] : s3[0];

endmodule

(* abc9_box, lib_whitebox *)
module NX_DFF(input I, CK, L, R, output reg O);

parameter dff_ctxt = 1'bx;
parameter dff_edge = 1'b0;
parameter dff_init = 1'b0;
parameter dff_load = 1'b0;
parameter dff_sync = 1'b0;
parameter dff_type = 1'b0;

initial begin
	O = dff_ctxt;
end

wire clock = CK ^ dff_edge;
wire load = dff_load ? L : 1'b1;
wire async_reset = !dff_sync && dff_init && R;
wire sync_reset = dff_sync && dff_init && R;

always @(posedge clock, posedge async_reset)
	if (async_reset) O <= dff_type;
	else if (sync_reset) O <= dff_type;
	else if (load) O <= I;

endmodule

(* abc9_box, lib_whitebox *)
module NX_DFR(input I, CK, L, R, output O);

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

wire clock = CK ^ dff_edge;
wire load = dff_load ? L : 1'b1;
wire async_reset = !dff_sync && dff_init && R;
wire sync_reset = dff_sync && dff_init && R;
reg O_reg;

always @(posedge clock, posedge async_reset)
	if (async_reset) O_reg <= dff_type;
	else if (sync_reset) O_reg <= dff_type;
	else if (load) O_reg <= I;

assign O = data_inv ? O_reg : ~O_reg;

endmodule


(* abc9_box, lib_whitebox *)
module NX_CY(input A1, A2, A3, A4, B1, B2, B3, B4, (* abc9_carry *) input CI, output S1, S2, S3, S4, (* abc9_carry *) output CO);
parameter add_carry = 0;

wire CI_1;
wire CO1, CO2, CO3;

assign  CI_1 = (add_carry==2) ? CI : ((add_carry==1) ? 1'b1 : 1'b0);

assign { CO1, S1 } = A1 + B1 + CI_1;
assign { CO2, S2 } = A2 + B2 + CO1;
assign { CO3, S3 } = A3 + B3 + CO2;
assign { CO,  S4 } = A4 + B4 + CO3;

endmodule

module NX_IOB(I, C, T, O, IO);
    input C;
    input I;
	(* iopad_external_pin *)
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

	assign O = IO;
	assign IO = C ? I : 1'bz;
endmodule

module NX_IOB_I(C, T, IO, O);
    input C;
	(* iopad_external_pin *)
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

	assign O = IO;
endmodule

module NX_IOB_O(I, C, T, IO);
    input C;
    input I;
	(* iopad_external_pin *)
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

	assign IO = C ? I : 1'bz;
endmodule

(* abc9_box, lib_whitebox *)
module NX_CY_1BIT(CI, A, B, S, CO);
    (* abc9_carry *)
    input CI;
    input A;
    input B;
    output S;
    (* abc9_carry *)
    output CO;
    parameter first = 1'b0;

    assign {CO, S} = A + B + CI;
endmodule

module NX_BD(I, O);
    input I;
    output O;
    parameter mode = "global_lowskew";

    assign O = I;
endmodule

module NX_BFF(I, O);
    input I;
    output O;

    assign O = I;
endmodule

module NX_BFR(I, O);
    input I;
    output O;
    parameter data_inv = 1'b0;
    parameter iobname = "";
    parameter location = "";
    parameter mode = 0;
    parameter path = 0;
    parameter ring = 0;

    assign O = data_inv ? ~I : I;
endmodule

(* abc9_box, lib_whitebox *)
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
    output reg AO1;
    output reg AO10;
    output reg AO11;
    output reg AO12;
    output reg AO13;
    output reg AO14;
    output reg AO15;
    output reg AO16;
    output reg AO17;
    output reg AO18;
    output reg AO19;
    output reg AO2;
    output reg AO20;
    output reg AO21;
    output reg AO22;
    output reg AO23;
    output reg AO24;
    output reg AO3;
    output reg AO4;
    output reg AO5;
    output reg AO6;
    output reg AO7;
    output reg AO8;
    output reg AO9;
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
    output reg BO1;
    output reg BO10;
    output reg BO11;
    output reg BO12;
    output reg BO13;
    output reg BO14;
    output reg BO15;
    output reg BO16;
    output reg BO17;
    output reg BO18;
    output reg BO19;
    output reg BO2;
    output reg BO20;
    output reg BO21;
    output reg BO22;
    output reg BO23;
    output reg BO24;
    output reg BO3;
    output reg BO4;
    output reg BO5;
    output reg BO6;
    output reg BO7;
    output reg BO8;
    output reg BO9;
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
    //parameter raw_l_enable = 1'b0;
    //parameter raw_l_extend = 4'b0000;
    //parameter raw_u_enable = 1'b0;
    //parameter raw_u_extend = 8'b00000000;
    parameter std_mode = "";

    reg [24-1:0] mem [2048-1:0]; // 48 Kbit of memory

    /*integer i;
    initial begin
        for (i = 0; i < 2048; i = i + 1)
            mem[i] = 24'b0;
    end*/

    wire [15:0] AA = { AA16, AA15, AA14, AA13, AA12, AA11, AA10, AA9, AA8, AA7, AA6, AA5, AA4, AA3, AA2, AA1 };
    wire [23:0] AI = { AI24, AI23, AI22, AI21, AI20, AI19, AI18, AI17, AI16, AI15, AI14, AI13, AI12, AI11, AI10, AI9, AI8, AI7, AI6, AI5, AI4, AI3, AI2, AI1 };
    wire [23:0] AO = { AO24, AO23, AO22, AO21, AO20, AO19, AO18, AO17, AO16, AO15, AO14, AO13, AO12, AO11, AO10, AO9, AO8, AO7, AO6, AO5, AO4, AO3, AO2, AO1 };
    wire [15:0] BA = { BA16, BA15, BA14, BA13, BA12, BA11, BA10, BA9, BA8, BA7, BA6, BA5, BA4, BA3, BA2, BA1 };
    wire [23:0] BI = { BI24, BI23, BI22, BI21, BI20, BI19, BI18, BI17, BI16, BI15, BI14, BI13, BI12, BI11, BI10, BI9, BI8, BI7, BI6, BI5, BI4, BI3, BI2, BI1 };
    wire [23:0] BO = { BO24, BO23, BO22, BO21, BO20, BO19, BO18, BO17, BO16, BO15, BO14, BO13, BO12, BO11, BO10, BO9, BO8, BO7, BO6, BO5, BO4, BO3, BO2, BO1 };

    always @(posedge ACK)
        if (AWE)
            mem[AA[10:0]] <= AI;
        else
            { AO24, AO23, AO22, AO21, AO20, AO19, AO18, AO17, AO16, AO15, AO14, AO13, AO12, AO11, AO10, AO9, AO8, AO7, AO6, AO5, AO4, AO3, AO2, AO1 } <= mem[AA[10:0]];
    assign ACOR = 1'b0;
    assign AERR = 1'b0;

    always @(posedge BCK)
        if (BWE)
            mem[BA[10:0]] <= BI;
        else
            { BO24, BO23, BO22, BO21, BO20, BO19, BO18, BO17, BO16, BO15, BO14, BO13, BO12, BO11, BO10, BO9, BO8, BO7, BO6, BO5, BO4, BO3, BO2, BO1 } <= mem[BA[10:0]];
    assign BCOR = 1'b0;
    assign BERR = 1'b0;
endmodule
