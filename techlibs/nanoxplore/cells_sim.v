module NX_LUT(input I1, I2, I3, I4, output O);

parameter lut_table = 16'h0000;

wire [7:0] s1 = I4 ? lut_table[15:8] : lut_table[7:0];
wire [3:0] s2 = I3 ? s1[7:4] : s1[3:0];
wire [1:0] s3 = I2 ? s2[3:2] : s2[1:0];
assign O = I1 ? s3[1] : s3[0];

endmodule

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
