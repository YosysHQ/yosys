
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

// SiliconBlue RAM Cells

module SB_RAM40_4K (
	output reg [15:0] RDATA,
	input             RCLK, RCLKE, RE,
	input      [10:0] RADDR,
	input             WCLK, WCLKE, WE,
	input      [10:0] WADDR,
	input      [15:0] MASK, WDATA
);
	// MODE 0:  256 x 16
	// MODE 1:  512 x 8
	// MODE 2: 1024 x 4
	// MODE 3: 2048 x 2
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

`ifndef BLACKBOX
	integer i;
	reg [15:0] memory [0:255];

	initial begin
		for (i=0; i<16; i=i+1) begin
			memory[ 0*16 + i] <= INIT_0[16*i +: 16];
			memory[ 1*16 + i] <= INIT_1[16*i +: 16];
			memory[ 2*16 + i] <= INIT_2[16*i +: 16];
			memory[ 3*16 + i] <= INIT_3[16*i +: 16];
			memory[ 4*16 + i] <= INIT_4[16*i +: 16];
			memory[ 5*16 + i] <= INIT_5[16*i +: 16];
			memory[ 6*16 + i] <= INIT_6[16*i +: 16];
			memory[ 7*16 + i] <= INIT_7[16*i +: 16];
			memory[ 8*16 + i] <= INIT_8[16*i +: 16];
			memory[ 9*16 + i] <= INIT_9[16*i +: 16];
			memory[10*16 + i] <= INIT_A[16*i +: 16];
			memory[11*16 + i] <= INIT_B[16*i +: 16];
			memory[12*16 + i] <= INIT_C[16*i +: 16];
			memory[13*16 + i] <= INIT_D[16*i +: 16];
			memory[14*16 + i] <= INIT_E[16*i +: 16];
			memory[15*16 + i] <= INIT_F[16*i +: 16];
		end
	end

	always @(posedge WCLK) begin
		if (WE && WCLKE) begin
			if (WRITE_MODE == 0) begin
				for (i=0; i<16; i=i+1)
					if (MASK[i]) memory[WADDR[7:0]][i] <= WDATA[i];
			end
			if (WRITE_MODE == 1) begin
				for (i=0; i<2; i=i+1)
					if (WADDR[0] == i) memory[WADDR[8:1]][i*8 +: 8] <= WDATA[i][7:0];
			end
			if (WRITE_MODE == 2) begin
				for (i=0; i<4; i=i+1)
					if (WADDR[1:0] == i) memory[WADDR[9:2]][i*4 +: 4] <= WDATA[i][3:0];
			end
			if (WRITE_MODE == 3) begin
				for (i=0; i<8; i=i+1)
					if (WADDR[2:0] == i) memory[WADDR[10:3]][i*2 +: 2] <= WDATA[i][1:0];
			end
		end
	end

	always @(posedge RCLK) begin
		if (RE && RCLKE) begin
			if (READ_MODE == 0) begin
				RDATA <= memory[RADDR[7:0]];
			end
			if (READ_MODE == 1) begin
				RDATA <= memory[RADDR[8:1]][RADDR[0]*8 +: 8];
			end
			if (READ_MODE == 2) begin
				RDATA <= memory[RADDR[9:2]][RADDR[1:0]*4 +: 4];
			end
			if (READ_MODE == 3) begin
				RDATA <= memory[RADDR[10:3]][RADDR[2:0]*2 +: 2];
			end
		end
	end
`endif
endmodule

module SB_RAM40_4KNR (
	output [15:0] RDATA,
	input         RCLK, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLK, WCLKE, WE,
	input  [10:0] WADDR,
	input  [15:0] MASK, WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    )
	) RAM (
		.RDATA(RDATA),
		.RCLK (~RCLK),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (WCLK ),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
endmodule

module SB_RAM40_4KNW (
	output [15:0] RDATA,
	input         RCLK, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLK, WCLKE, WE,
	input  [10:0] WADDR,
	input  [15:0] MASK, WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    )
	) RAM (
		.RDATA(RDATA),
		.RCLK (RCLK ),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (~WCLK),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
endmodule

module SB_RAM40_4KNRNW (
	output [15:0] RDATA,
	input         RCLK, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLK, WCLKE, WE,
	input  [10:0] WADDR,
	input  [15:0] MASK, WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    )
	) RAM (
		.RDATA(RDATA),
		.RCLK (~RCLK),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (~WCLK),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
endmodule

// Packed IceStorm Logic Cells

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

	reg o_reg;
	always @(posedge polarized_clk)
		if (CEN)
			o_reg <= SR ? SET_NORESET : lut_o;

	reg o_reg_async;
	always @(posedge polarized_clk, posedge SR)
		if (SR)
			o_reg <= SET_NORESET;
		else if (CEN)
			o_reg <= lut_o;

	assign O = DFF_ENABLE ? ASYNC_SR ? o_reg_async : o_reg : lut_o;
endmodule

