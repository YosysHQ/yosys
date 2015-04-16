
// SiliconBlue IO Cells

module SB_IO (
	inout  PACKAGE_PIN,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0; 
	parameter IO_STANDARD = "SB_LVCMOS";

	/* TBD */
endmodule

module SB_GB_IO (
	inout  PACKAGE_PIN,
	output GLOBAL_BUFFER_OUTPUT,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0; 
	parameter IO_STANDARD = "SB_LVCMOS";

	assign GLOBAL_BUFFER_OUTPUT = PACKAGE_PIN;

	SB_IO #(
		.PIN_TYPE(PIN_TYPE),
		.PULLUP(PULLUP),
		.NEG_TRIGGER(NEG_TRIGGER),
		.IO_STANDARD(IO_STANDARD)
	) IO (
		.PACKAGE_PIN(PACKAGE_PIN),
		.LATCH_INPUT_VALUE(LATCH_INPUT_VALUE),
		.CLOCK_ENABLE(CLOCK_ENABLE),
		.INPUT_CLK(INPUT_CLK),
		.OUTPUT_CLK(OUTPUT_CLK),
		.OUTPUT_ENABLE(OUTPUT_ENABLE),
		.D_OUT_0(D_OUT_0),
		.D_OUT_1(D_OUT_1),
		.D_IN_0(D_IN_0),
		.D_IN_1(D_IN_1)
	);
endmodule

module SB_GB (
	input  USER_SIGNAL_TO_GLOBAL_BUFFER,
	output GLOBAL_BUFFER_OUTPUT
);
	assign GLOBAL_BUFFER_OUTPUT = USER_SIGNAL_TO_GLOBAL_BUFFER;
endmodule

// SiliconBlue Logic Cells

module SB_LUT4 (output O, input I0, I1, I2, I3);
	parameter [15:0] LUT_INIT = 0;
	wire [7:0] s3 = I3 ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] s2 = I2 ?       s3[ 7:4] :       s3[3:0];
	wire [1:0] s1 = I1 ?       s2[ 3:2] :       s2[1:0];
	assign O = I0 ? s1[1] : s1[0];
endmodule

module SB_CARRY (output CO, input I0, I1, CI);
	assign CO = (I0 && I1) || ((I0 || I1) && CI);
endmodule

// Positive Edge SiliconBlue FF Cells

module SB_DFF (output reg Q, input C, D);
	always @(posedge C)
		Q <= D;
endmodule

module SB_DFFE (output reg Q, input C, E, D);
	always @(posedge C)
		if (E)
			Q <= D;
endmodule

module SB_DFFSR (output reg Q, input C, R, D);
	always @(posedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFR (output reg Q, input C, R, D);
	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFSS (output reg Q, input C, S, D);
	always @(posedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFS (output reg Q, input C, S, D);
	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFESR (output reg Q, input C, E, R, D);
	always @(posedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
endmodule

module SB_DFFER (output reg Q, input C, E, R, D);
	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
endmodule

module SB_DFFESS (output reg Q, input C, E, S, D);
	always @(posedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
endmodule

module SB_DFFES (output reg Q, input C, E, S, D);
	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
endmodule

// Negative Edge SiliconBlue FF Cells

module SB_DFFN (output reg Q, input C, D);
	always @(negedge C)
		Q <= D;
endmodule

module SB_DFFNE (output reg Q, input C, E, D);
	always @(negedge C)
		if (E)
			Q <= D;
endmodule

module SB_DFFNSR (output reg Q, input C, R, D);
	always @(negedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFNR (output reg Q, input C, R, D);
	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFNSS (output reg Q, input C, S, D);
	always @(negedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFNS (output reg Q, input C, S, D);
	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFNESR (output reg Q, input C, E, R, D);
	always @(negedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
endmodule

module SB_DFFNER (output reg Q, input C, E, R, D);
	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
endmodule

module SB_DFFNESS (output reg Q, input C, E, S, D);
	always @(negedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
endmodule

module SB_DFFNES (output reg Q, input C, E, S, D);
	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
endmodule

// Packed IceStorm Logic Cells

module ICESTORM_CARRYCONST (output O);
	parameter [0:0] CARRYCONST = 0;
	assign O = CARRYCONST;
endmodule

module ICESTORM_LC (
	input I0, I1, I2, I3, CIN, CLK, CEN, SR,
	output O, COUT
);
	parameter [15:0] LUT_INIT = 0;

	parameter [0:0] NEG_CLK      = 0;
	parameter [0:0] CARRY_ENABLE = 0;
	parameter [0:0] DFF_ENABLE   = 0;
	parameter [0:0] SET_NORESET  = 0;
	parameter [0:0] ASYNC_SR     = 0;

	wire COUT = CARRY_ENABLE ? (I1 && I2) || ((I1 || I2) && CIN) : 1'bx;

	wire [7:0] lut_s3 = I3 ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] lut_s2 = I2 ?   lut_s3[ 7:4] :   lut_s3[3:0];
	wire [1:0] lut_s1 = I1 ?   lut_s2[ 3:2] :   lut_s2[1:0];
	wire       lut_o  = I0 ?   lut_s1[   1] :   lut_s1[  0];

	wire polarized_clk;
	assign polarized_clk = CLK ^ NEG_CLK;

	wire filtered_cen, filtered_sr;
	assign filtered_cen = CEN === 1'bz ? 1'b1 : CEN;
	assign filtered_sr = SR === 1'bz ? 1'b0 : SR;

	reg o_reg;
	always @(posedge polarized_clk)
		if (filtered_cen)
			o_reg <= filtered_sr ? SET_NORESET : lut_o;

	reg o_reg_async;
	always @(posedge polarized_clk, posedge filtered_sr)
		if (filtered_sr)
			o_reg <= SET_NORESET;
		else if (filtered_cen)
			o_reg <= lut_o;

	assign O = DFF_ENABLE ? ASYNC_SR ? o_reg_async : o_reg : lut_o;
endmodule

