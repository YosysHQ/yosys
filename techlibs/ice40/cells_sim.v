
`define SB_DFF_REG reg Q = 0
// `define SB_DFF_REG reg Q

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

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end else begin
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCH_INPUT_VALUE)
			din_0 = PIN_TYPE[0] ? PACKAGE_PIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUT_CLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : D_OUT_0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign D_IN_0 = din_0, D_IN_1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGE_PIN = dout;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGE_PIN = OUTPUT_ENABLE ? dout : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGE_PIN = outena_q ? dout : 1'bz;
	endgenerate
`endif
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

module SB_DFF (output `SB_DFF_REG, input C, D);
	always @(posedge C)
		Q <= D;
endmodule

module SB_DFFE (output `SB_DFF_REG, input C, E, D);
	always @(posedge C)
		if (E)
			Q <= D;
endmodule

module SB_DFFSR (output `SB_DFF_REG, input C, R, D);
	always @(posedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFR (output `SB_DFF_REG, input C, R, D);
	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFSS (output `SB_DFF_REG, input C, S, D);
	always @(posedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFS (output `SB_DFF_REG, input C, S, D);
	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFESR (output `SB_DFF_REG, input C, E, R, D);
	always @(posedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
endmodule

module SB_DFFER (output `SB_DFF_REG, input C, E, R, D);
	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
endmodule

module SB_DFFESS (output `SB_DFF_REG, input C, E, S, D);
	always @(posedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
endmodule

module SB_DFFES (output `SB_DFF_REG, input C, E, S, D);
	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
endmodule

// Negative Edge SiliconBlue FF Cells

module SB_DFFN (output `SB_DFF_REG, input C, D);
	always @(negedge C)
		Q <= D;
endmodule

module SB_DFFNE (output `SB_DFF_REG, input C, E, D);
	always @(negedge C)
		if (E)
			Q <= D;
endmodule

module SB_DFFNSR (output `SB_DFF_REG, input C, R, D);
	always @(negedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFNR (output `SB_DFF_REG, input C, R, D);
	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
endmodule

module SB_DFFNSS (output `SB_DFF_REG, input C, S, D);
	always @(negedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFNS (output `SB_DFF_REG, input C, S, D);
	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
endmodule

module SB_DFFNESR (output `SB_DFF_REG, input C, E, R, D);
	always @(negedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
endmodule

module SB_DFFNER (output `SB_DFF_REG, input C, E, R, D);
	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
endmodule

module SB_DFFNESS (output `SB_DFF_REG, input C, E, S, D);
	always @(negedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
endmodule

module SB_DFFNES (output `SB_DFF_REG, input C, E, S, D);
	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
endmodule

// SiliconBlue RAM Cells

module SB_RAM40_4K (
	output [15:0] RDATA,
	input         RCLK, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLK, WCLKE, WE,
	input  [10:0] WADDR,
	input  [15:0] MASK, WDATA
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
	wire [15:0] WMASK_I;
	wire [15:0] RMASK_I;

	reg  [15:0] RDATA_I;
	wire [15:0] WDATA_I;

	generate
		case (WRITE_MODE)
			0: assign WMASK_I = MASK;

			1: assign WMASK_I = WADDR[   8] == 0 ? 16'b 1010_1010_1010_1010 :
			                    WADDR[   8] == 1 ? 16'b 0101_0101_0101_0101 : 16'bx;

			2: assign WMASK_I = WADDR[ 9:8] == 0 ? 16'b 1110_1110_1110_1110 :
			                    WADDR[ 9:8] == 1 ? 16'b 1101_1101_1101_1101 :
			                    WADDR[ 9:8] == 2 ? 16'b 1011_1011_1011_1011 :
			                    WADDR[ 9:8] == 3 ? 16'b 0111_0111_0111_0111 : 16'bx;

			3: assign WMASK_I = WADDR[10:8] == 0 ? 16'b 1111_1110_1111_1110 :
			                    WADDR[10:8] == 1 ? 16'b 1111_1101_1111_1101 :
			                    WADDR[10:8] == 2 ? 16'b 1111_1011_1111_1011 :
			                    WADDR[10:8] == 3 ? 16'b 1111_0111_1111_0111 :
			                    WADDR[10:8] == 4 ? 16'b 1110_1111_1110_1111 :
			                    WADDR[10:8] == 5 ? 16'b 1101_1111_1101_1111 :
			                    WADDR[10:8] == 6 ? 16'b 1011_1111_1011_1111 :
			                    WADDR[10:8] == 7 ? 16'b 0111_1111_0111_1111 : 16'bx;
		endcase

		case (READ_MODE)
			0: assign RMASK_I = 16'b 0000_0000_0000_0000;

			1: assign RMASK_I = RADDR[   8] == 0 ? 16'b 1010_1010_1010_1010 :
			                    RADDR[   8] == 1 ? 16'b 0101_0101_0101_0101 : 16'bx;

			2: assign RMASK_I = RADDR[ 9:8] == 0 ? 16'b 1110_1110_1110_1110 :
			                    RADDR[ 9:8] == 1 ? 16'b 1101_1101_1101_1101 :
			                    RADDR[ 9:8] == 2 ? 16'b 1011_1011_1011_1011 :
			                    RADDR[ 9:8] == 3 ? 16'b 0111_0111_0111_0111 : 16'bx;

			3: assign RMASK_I = RADDR[10:8] == 0 ? 16'b 1111_1110_1111_1110 :
			                    RADDR[10:8] == 1 ? 16'b 1111_1101_1111_1101 :
			                    RADDR[10:8] == 2 ? 16'b 1111_1011_1111_1011 :
			                    RADDR[10:8] == 3 ? 16'b 1111_0111_1111_0111 :
			                    RADDR[10:8] == 4 ? 16'b 1110_1111_1110_1111 :
			                    RADDR[10:8] == 5 ? 16'b 1101_1111_1101_1111 :
			                    RADDR[10:8] == 6 ? 16'b 1011_1111_1011_1111 :
			                    RADDR[10:8] == 7 ? 16'b 0111_1111_0111_1111 : 16'bx;
		endcase

		case (WRITE_MODE)
			0: assign WDATA_I = WDATA;

			1: assign WDATA_I = {WDATA[14], WDATA[14], WDATA[12], WDATA[12],
			                     WDATA[10], WDATA[10], WDATA[ 8], WDATA[ 8],
			                     WDATA[ 6], WDATA[ 6], WDATA[ 4], WDATA[ 4],
			                     WDATA[ 2], WDATA[ 2], WDATA[ 0], WDATA[ 0]};

			2: assign WDATA_I = {WDATA[13], WDATA[13], WDATA[13], WDATA[13],
			                     WDATA[ 9], WDATA[ 9], WDATA[ 9], WDATA[ 9],
			                     WDATA[ 5], WDATA[ 5], WDATA[ 5], WDATA[ 5],
			                     WDATA[ 1], WDATA[ 1], WDATA[ 1], WDATA[ 1]};

			3: assign WDATA_I = {WDATA[11], WDATA[11], WDATA[11], WDATA[11],
			                     WDATA[11], WDATA[11], WDATA[11], WDATA[11],
			                     WDATA[ 3], WDATA[ 3], WDATA[ 3], WDATA[ 3],
			                     WDATA[ 3], WDATA[ 3], WDATA[ 3], WDATA[ 3]};
		endcase

		case (READ_MODE)
			0: assign RDATA = RDATA_I;
			1: assign RDATA = {1'b0, |RDATA_I[15:14], 1'b0, |RDATA_I[13:12], 1'b0, |RDATA_I[11:10], 1'b0, |RDATA_I[ 9: 8],
			                   1'b0, |RDATA_I[ 7: 6], 1'b0, |RDATA_I[ 5: 4], 1'b0, |RDATA_I[ 3: 2], 1'b0, |RDATA_I[ 1: 0]};
			2: assign RDATA = {2'b0, |RDATA_I[15:12], 3'b0, |RDATA_I[11: 8], 3'b0, |RDATA_I[ 7: 4], 3'b0, |RDATA_I[ 3: 0], 1'b0};
			3: assign RDATA = {4'b0, |RDATA_I[15: 8], 7'b0, |RDATA_I[ 7: 0], 3'b0};
		endcase
	endgenerate

	integer i;
	reg [15:0] memory [0:255];

	initial begin
		for (i=0; i<16; i=i+1) begin
			memory[ 0*16 + i] = INIT_0[16*i +: 16];
			memory[ 1*16 + i] = INIT_1[16*i +: 16];
			memory[ 2*16 + i] = INIT_2[16*i +: 16];
			memory[ 3*16 + i] = INIT_3[16*i +: 16];
			memory[ 4*16 + i] = INIT_4[16*i +: 16];
			memory[ 5*16 + i] = INIT_5[16*i +: 16];
			memory[ 6*16 + i] = INIT_6[16*i +: 16];
			memory[ 7*16 + i] = INIT_7[16*i +: 16];
			memory[ 8*16 + i] = INIT_8[16*i +: 16];
			memory[ 9*16 + i] = INIT_9[16*i +: 16];
			memory[10*16 + i] = INIT_A[16*i +: 16];
			memory[11*16 + i] = INIT_B[16*i +: 16];
			memory[12*16 + i] = INIT_C[16*i +: 16];
			memory[13*16 + i] = INIT_D[16*i +: 16];
			memory[14*16 + i] = INIT_E[16*i +: 16];
			memory[15*16 + i] = INIT_F[16*i +: 16];
		end
	end

	always @(posedge WCLK) begin
		if (WE && WCLKE) begin
			if (!WMASK_I[ 0]) memory[WADDR[7:0]][ 0] <= WDATA_I[ 0];
			if (!WMASK_I[ 1]) memory[WADDR[7:0]][ 1] <= WDATA_I[ 1];
			if (!WMASK_I[ 2]) memory[WADDR[7:0]][ 2] <= WDATA_I[ 2];
			if (!WMASK_I[ 3]) memory[WADDR[7:0]][ 3] <= WDATA_I[ 3];
			if (!WMASK_I[ 4]) memory[WADDR[7:0]][ 4] <= WDATA_I[ 4];
			if (!WMASK_I[ 5]) memory[WADDR[7:0]][ 5] <= WDATA_I[ 5];
			if (!WMASK_I[ 6]) memory[WADDR[7:0]][ 6] <= WDATA_I[ 6];
			if (!WMASK_I[ 7]) memory[WADDR[7:0]][ 7] <= WDATA_I[ 7];
			if (!WMASK_I[ 8]) memory[WADDR[7:0]][ 8] <= WDATA_I[ 8];
			if (!WMASK_I[ 9]) memory[WADDR[7:0]][ 9] <= WDATA_I[ 9];
			if (!WMASK_I[10]) memory[WADDR[7:0]][10] <= WDATA_I[10];
			if (!WMASK_I[11]) memory[WADDR[7:0]][11] <= WDATA_I[11];
			if (!WMASK_I[12]) memory[WADDR[7:0]][12] <= WDATA_I[12];
			if (!WMASK_I[13]) memory[WADDR[7:0]][13] <= WDATA_I[13];
			if (!WMASK_I[14]) memory[WADDR[7:0]][14] <= WDATA_I[14];
			if (!WMASK_I[15]) memory[WADDR[7:0]][15] <= WDATA_I[15];
		end
	end

	always @(posedge RCLK) begin
		if (RE && RCLKE) begin
			RDATA_I <= memory[RADDR[7:0]] & ~RMASK_I;
		end
	end
`endif
endmodule

module SB_RAM40_4KNR (
	output [15:0] RDATA,
	input         RCLKN, RCLKE, RE,
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
		.RCLK (~RCLKN),
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
	input         WCLKN, WCLKE, WE,
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
		.WCLK (~WCLKN),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
endmodule

module SB_RAM40_4KNRNW (
	output [15:0] RDATA,
	input         RCLKN, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLKN, WCLKE, WE,
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
		.RCLK (~RCLKN),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (~WCLKN),
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
	output LO, O, COUT
);
	parameter [15:0] LUT_INIT = 0;

	parameter [0:0] NEG_CLK      = 0;
	parameter [0:0] CARRY_ENABLE = 0;
	parameter [0:0] DFF_ENABLE   = 0;
	parameter [0:0] SET_NORESET  = 0;
	parameter [0:0] ASYNC_SR     = 0;

	parameter [0:0] CIN_CONST    = 0;
	parameter [0:0] CIN_SET      = 0;

	wire mux_cin = CIN_CONST ? CIN_SET : CIN;

	assign COUT = CARRY_ENABLE ? (I1 && I2) || ((I1 || I2) && mux_cin) : 1'bx;

	wire [7:0] lut_s3 = I3 ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] lut_s2 = I2 ?   lut_s3[ 7:4] :   lut_s3[3:0];
	wire [1:0] lut_s1 = I1 ?   lut_s2[ 3:2] :   lut_s2[1:0];
	wire       lut_o  = I0 ?   lut_s1[   1] :   lut_s1[  0];

	assign LO = lut_o;

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

// SiliconBlue PLL Cells

(* blackbox *)
module SB_PLL40_CORE (
	input   REFERENCECLK,
	output  PLLOUTCORE,
	output  PLLOUTGLOBAL,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCORE,
	output  PLLOUTGLOBAL,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2F_CORE (
	input   REFERENCECLK,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTA = "GENCLK";
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2F_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 2'b00;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTA = "GENCLK";
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

// SiliconBlue Device Configuration Cells

(* blackbox, keep *)
module SB_WARMBOOT (
	input BOOT,
	input S1,
	input S0
);
endmodule

// UltraPlus feature cells
(* blackbox *)
module SB_MAC16 (
	input CLK,
	input CE,
	input [15:0] C,
	input [15:0] A,
	input [15:0] B,
	input [15:0] D,
	input AHOLD,
	input BHOLD,
	input CHOLD,
	input DHOLD,
	input IRSTTOP,
	input IRSTBOT,
	input ORSTTOP,
	input ORSTBOT,
	input OLOADTOP,
	input OLOADBOT,
	input ADDSUBTOP,
	input ADDSUBBOT,
	input OHOLDTOP,
	input OHOLDBOT,
	input CI,
	input ACCUMCI,
	input SIGNEXTIN,
	output [31:0] O,
	output CO,
	output ACCUMCO,
	output SIGNEXTOUT
);
parameter NEG_TRIGGER = 1'b0;
parameter C_REG = 1'b0;
parameter A_REG = 1'b0;
parameter B_REG = 1'b0;
parameter D_REG = 1'b0;
parameter TOP_8x8_MULT_REG = 1'b0;
parameter BOT_8x8_MULT_REG = 1'b0;
parameter PIPELINE_16x16_MULT_REG1 = 1'b0;
parameter PIPELINE_16x16_MULT_REG2 = 1'b0;
parameter TOPOUTPUT_SELECT =  2'b00;
parameter TOPADDSUB_LOWERINPUT = 2'b00;
parameter TOPADDSUB_UPPERINPUT = 1'b0;
parameter TOPADDSUB_CARRYSELECT = 2'b00;
parameter BOTOUTPUT_SELECT =  2'b00;
parameter BOTADDSUB_LOWERINPUT = 2'b00;
parameter BOTADDSUB_UPPERINPUT = 1'b0;
parameter BOTADDSUB_CARRYSELECT = 2'b00;
parameter MODE_8x8 = 1'b0;
parameter A_SIGNED = 1'b0;
parameter B_SIGNED = 1'b0;
endmodule

module SB_SPRAM256KA (
	input [13:0] ADDRESS,
	input [15:0] DATAIN,
	input [3:0] MASKWREN,
	input WREN, CHIPSELECT, CLOCK, STANDBY, SLEEP, POWEROFF,
	output reg [15:0] DATAOUT
);
`ifndef BLACKBOX
	reg [15:0] mem [0:16383];
	wire off = SLEEP || !POWEROFF;
	integer i;

	always @(negedge POWEROFF) begin
		for (i = 0; i <= 16383; i = i+1)
			mem[i] = 'bx;
	end

	always @(posedge CLOCK, posedge off) begin
		if (off) begin
			DATAOUT <= 0;
		end else
		if (CHIPSELECT && !STANDBY && !WREN) begin
			DATAOUT <= mem[ADDRESS];
		end else begin
			if (CHIPSELECT && !STANDBY && WREN) begin
				if (MASKWREN[0]) mem[ADDRESS][ 3: 0] = DATAIN[ 3: 0];
				if (MASKWREN[1]) mem[ADDRESS][ 7: 4] = DATAIN[ 7: 4];
				if (MASKWREN[2]) mem[ADDRESS][11: 8] = DATAIN[11: 8];
				if (MASKWREN[3]) mem[ADDRESS][15:12] = DATAIN[15:12];
			end
			DATAOUT <= 'bx;
		end
	end
`endif
endmodule

(* blackbox *)
module SB_HFOSC(
	input CLKHFPU,
	input CLKHFEN,
	output CLKHF
);
parameter CLKHF_DIV = "0b00";
endmodule

(* blackbox *)
module SB_LFOSC(
	input CLKLFPU,
	input CLKLFEN,
	output CLKLF
);
endmodule

(* blackbox *)
module SB_RGBA_DRV(
	input CURREN,
	input RGBLEDEN,
	input RGB0PWM,
	input RGB1PWM,
	input RGB2PWM,
	output RGB0,
	output RGB1,
	output RGB2
);
parameter CURRENT_MODE = "0b0";
parameter RGB0_CURRENT = "0b000000";
parameter RGB1_CURRENT = "0b000000";
parameter RGB2_CURRENT = "0b000000";
endmodule

(* blackbox *)
module SB_I2C(
	input  SBCLKI,
	input  SBRWI,
	input  SBSTBI,
	input  SBADRI7,
	input  SBADRI6,
	input  SBADRI5,
	input  SBADRI4,
	input  SBADRI3,
	input  SBADRI2,
	input  SBADRI1,
	input  SBADRI0,
	input  SBDATI7,
	input  SBDATI6,
	input  SBDATI5,
	input  SBDATI4,
	input  SBDATI3,
	input  SBDATI2,
	input  SBDATI1,
	input  SBDATI0,
	input  SCLI,
	input  SDAI,
	output SBDATO7,
	output SBDATO6,
	output SBDATO5,
	output SBDATO4,
	output SBDATO3,
	output SBDATO2,
	output SBDATO1,
	output SBDATO0,
	output SBACKO,
	output I2CIRQ,
	output I2CWKUP,
	output SCLO, //inout in the SB verilog library, but output in the VHDL and PDF libs and seemingly in the HW itself
	output SCLOE,
	output SDAO,
	output SDAOE
);
parameter I2C_SLAVE_INIT_ADDR = "0b1111100001";
parameter BUS_ADDR74 = "0b0001";
endmodule

(* blackbox *)
module SB_SPI (
	input  SBCLKI,
	input  SBRWI,
	input  SBSTBI,
	input  SBADRI7,
	input  SBADRI6,
	input  SBADRI5,
	input  SBADRI4,
	input  SBADRI3,
	input  SBADRI2,
	input  SBADRI1,
	input  SBADRI0,
	input  SBDATI7,
	input  SBDATI6,
	input  SBDATI5,
	input  SBDATI4,
	input  SBDATI3,
	input  SBDATI2,
	input  SBDATI1,
	input  SBDATI0,
	input  MI,
	input  SI,
	input  SCKI,
	input  SCSNI,
	output SBDATO7,
	output SBDATO6,
	output SBDATO5,
	output SBDATO4,
	output SBDATO3,
	output SBDATO2,
	output SBDATO1,
	output SBDATO0,
	output SBACKO,
	output SPIIRQ,
	output SPIWKUP,
	output SO,
	output SOE,
	output MO,
	output MOE,
	output SCKO, //inout in the SB verilog library, but output in the VHDL and PDF libs and seemingly in the HW itself
	output SCKOE,
	output MCSNO3,
	output MCSNO2,
	output MCSNO1,
	output MCSNO0,
	output MCSNOE3,
	output MCSNOE2,
	output MCSNOE1,
	output MCSNOE0
);
parameter BUS_ADDR74 = "0b0000";
endmodule

(* blackbox *)
module SB_LEDDA_IP(
	input LEDDCS,
	input LEDDCLK,
	input LEDDDAT7,
	input LEDDDAT6,
	input LEDDDAT5,
	input LEDDDAT4,
	input LEDDDAT3,
	input LEDDDAT2,
	input LEDDDAT1,
	input LEDDDAT0,
	input LEDDADDR3,
	input LEDDADDR2,
	input LEDDADDR1,
	input LEDDADDR0,
	input LEDDDEN,
	input LEDDEXE,
	input LEDDRST,
	output PWMOUT0,
	output PWMOUT1,
	output PWMOUT2,
	output LEDDON
);
endmodule

(* blackbox *)
module SB_FILTER_50NS(
	input FILTERIN,
	output FILTEROUT
);
endmodule

module SB_IO_I3C (
	inout  PACKAGE_PIN,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1,
	input  PU_ENB,
	input  WEAK_PU_ENB
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] WEAK_PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0;
	parameter IO_STANDARD = "SB_LVCMOS";

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end else begin
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCH_INPUT_VALUE)
			din_0 = PIN_TYPE[0] ? PACKAGE_PIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUT_CLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : D_OUT_0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign D_IN_0 = din_0, D_IN_1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGE_PIN = dout;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGE_PIN = OUTPUT_ENABLE ? dout : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGE_PIN = outena_q ? dout : 1'bz;
	endgenerate
`endif
endmodule

module SB_IO_OD (
	inout  PACKAGEPIN,
	input  LATCHINPUTVALUE,
	input  CLOCKENABLE,
	input  INPUTCLK,
	input  OUTPUTCLK,
	input  OUTPUTENABLE,
	input  DOUT1,
	input  DOUT0,
	output DIN1,
	output DIN0
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] NEG_TRIGGER = 1'b0;

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUTCLK)  if (CLOCKENABLE) din_q_0  <= PACKAGEPIN;
		always @(negedge INPUTCLK)  if (CLOCKENABLE) din_q_1  <= PACKAGEPIN;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) dout_q_0 <= DOUT0;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) dout_q_1 <= DOUT1;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) outena_q <= OUTPUTENABLE;
	end else begin
		always @(negedge INPUTCLK)  if (CLOCKENABLE) din_q_0  <= PACKAGEPIN;
		always @(posedge INPUTCLK)  if (CLOCKENABLE) din_q_1  <= PACKAGEPIN;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) dout_q_0 <= DOUT0;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) dout_q_1 <= DOUT1;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) outena_q <= OUTPUTENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCHINPUTVALUE)
			din_0 = PIN_TYPE[0] ? PACKAGEPIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUTCLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : DOUT0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign DIN0 = din_0, DIN1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGEPIN = dout ? 1'bz : 1'b0;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGEPIN = OUTPUTENABLE ? (dout ? 1'bz : 1'b0) : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGEPIN = outena_q ? (dout ? 1'bz : 1'b0) : 1'bz;
	endgenerate
`endif
endmodule
