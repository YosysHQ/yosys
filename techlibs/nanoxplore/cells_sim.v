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

(* abc9_box, lib_whitebox *)
module NX_XRFB_64x18(input WCK, input [17:0] I, input [5:0] RA, WA, input WE, WEA, output [17:0] O);

parameter wck_edge = 1'b0;
parameter mem_ctxt = 1152'b0;

reg [17:0] mem [63:0];

integer i;
initial begin
	for (i = 0; i < 64; i = i + 1)
		mem[i] = mem_ctxt[18*i +: 18];
end

wire clock = WCK ^ wck_edge;

always @(posedge clock)
	if (WE && WEA)
		mem[WA] <= I;

assign O = mem[RA];

endmodule

(* abc9_box, lib_whitebox *)
module NX_XRFB_32x36(input WCK, input [35:0] I, input [4:0] RA, WA, input WE, WEA, output [35:0] O);

parameter wck_edge = 1'b0;
parameter mem_ctxt = 1152'b0;

reg [35:0] mem [31:0];

integer i;
initial begin
	for (i = 0; i < 32; i = i + 1)
		mem[i] = mem_ctxt[36*i +: 36];
end

wire clock = WCK ^ wck_edge;

always @(posedge clock)
	if (WE && WEA)
		mem[WA] <= I;

assign O = mem[RA];

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
