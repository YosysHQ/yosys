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
wire load = (dff_type == 2) ? (dff_load ? L : 1'bx) : dff_type;
wire async_reset = !dff_sync && dff_init && R;
wire sync_reset = dff_sync && dff_init && R;

always @(posedge clock, posedge async_reset)
	if (async_reset) O <= load;
	else if (sync_reset) O <= load;
	else O <= I;

endmodule

(* abc9_box, lib_whitebox *)
module NX_CY(input A1, A2, A3, A4, B1, B2, B3, B4, (* abc9_carry *) input CI, output S1, S2, S3, S4, (* abc9_carry *) output CO);
parameter add_carry = 0;

assign {CO, S4, S3, S2, S1} = {A4, A3, A2, A1} + {B4, B3, B2, B1} + CI;

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
