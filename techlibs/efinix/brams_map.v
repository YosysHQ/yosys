module \$__EFINIX_5K (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 8;
	parameter CFG_DBITS = 20;
	parameter CFG_ENABLE_A = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [5119:0] INIT = 5119'bx;
	parameter TRANSP2 = 0;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	input [CFG_DBITS-1:0] A1DATA;
	input [CFG_ENABLE_A-1:0] A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	output [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	localparam WRITEMODE_A = TRANSP2 ? "WRITE_FIRST" : "READ_FIRST";

	EFX_RAM_5K #(
   		.READ_WIDTH(CFG_DBITS),
   		.WRITE_WIDTH(CFG_DBITS),
   		.OUTPUT_REG(1'b0),
   		.RCLK_POLARITY(1'b1),
   		.RE_POLARITY(1'b1),
   		.WCLK_POLARITY(1'b1),
   		.WE_POLARITY(1'b1),
   		.WCLKE_POLARITY(1'b1),
   		.WRITE_MODE(WRITEMODE_A),
		.INIT_0(INIT[ 0*256 +: 256]),
		.INIT_1(INIT[ 1*256 +: 256]),
		.INIT_2(INIT[ 2*256 +: 256]),
		.INIT_3(INIT[ 3*256 +: 256]),
		.INIT_4(INIT[ 4*256 +: 256]),
		.INIT_5(INIT[ 5*256 +: 256]),
		.INIT_6(INIT[ 6*256 +: 256]),
		.INIT_7(INIT[ 7*256 +: 256]),
		.INIT_8(INIT[ 8*256 +: 256]),
		.INIT_9(INIT[ 9*256 +: 256]),
		.INIT_A(INIT[10*256 +: 256]),
		.INIT_B(INIT[11*256 +: 256]),
		.INIT_C(INIT[12*256 +: 256]),
		.INIT_D(INIT[13*256 +: 256]),
		.INIT_E(INIT[14*256 +: 256]),
		.INIT_F(INIT[15*256 +: 256]),
		.INIT_10(INIT[16*256 +: 256]),
		.INIT_11(INIT[17*256 +: 256]),
		.INIT_12(INIT[18*256 +: 256]),
		.INIT_13(INIT[19*256 +: 256])
	) _TECHMAP_REPLACE_ (
   		.WDATA(A1DATA),
   		.WADDR(A1ADDR),
   		.WE(A1EN),
   		.WCLK(CLK2),
   		.WCLKE(1'b1),
   		.RDATA(B1DATA),
   		.RADDR(B1ADDR),
   		.RE(B1EN),
   		.RCLK(CLK3)
	);
endmodule
