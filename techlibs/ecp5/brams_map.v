module \$__ECP5_DP16KD (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 10;
	parameter CFG_DBITS = 18;
	parameter CFG_ENABLE_A = 2;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [18431:0] INIT = 18432'bx;
	parameter TRANSP2 = 0;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	input [CFG_DBITS-1:0] A1DATA;
	input [CFG_ENABLE_A-1:0] A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	output [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	localparam CLKAMUX = CLKPOL2 ? "CLKA" : "INV";
	localparam CLKBMUX = CLKPOL3 ? "CLKB" : "INV";

	localparam WRITEMODE_A = TRANSP2 ? "WRITETHROUGH" : "READBEFOREWRITE";

	generate if (CFG_DBITS == 1) begin
		DP16KD #(
			`include "bram_init_1_2_4.vh"
			.DATA_WIDTH_A(1),
			.DATA_WIDTH_B(1),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WRITEMODE_A(WRITEMODE_A),
			.WRITEMODE_B("READBEFOREWRITE"),
			.GSR("AUTO")
		) _TECHMAP_REPLACE_ (
			`include "bram_conn_1.vh"
			.CLKA(CLK2), .CLKB(CLK3),
			.WEA(|A1EN), .CEA(1'b1), .OCEA(1'b1),
			.WEB(1'b0), .CEB(B1EN), .OCEB(1'b1),
			.RSTA(1'b0), .RSTB(1'b0)
		);
	end else if (CFG_DBITS == 2) begin
		DP16KD #(
			`include "bram_init_1_2_4.vh"
			.DATA_WIDTH_A(2),
			.DATA_WIDTH_B(2),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WRITEMODE_A(WRITEMODE_A),
			.WRITEMODE_B("READBEFOREWRITE"),
			.GSR("AUTO")
		) _TECHMAP_REPLACE_ (
			`include "bram_conn_2.vh"
			.CLKA(CLK2), .CLKB(CLK3),
			.WEA(|A1EN), .CEA(1'b1), .OCEA(1'b1),
			.WEB(1'b0), .CEB(B1EN), .OCEB(1'b1),
			.RSTA(1'b0), .RSTB(1'b0)
		);
	end else if (CFG_DBITS <= 4) begin
		DP16KD #(
			`include "bram_init_1_2_4.vh"
			.DATA_WIDTH_A(4),
			.DATA_WIDTH_B(4),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WRITEMODE_A(WRITEMODE_A),
			.WRITEMODE_B("READBEFOREWRITE"),
			.GSR("AUTO")
		) _TECHMAP_REPLACE_ (
			`include "bram_conn_4.vh"
			.CLKA(CLK2), .CLKB(CLK3),
			.WEA(|A1EN), .CEA(1'b1), .OCEA(1'b1),
			.WEB(1'b0), .CEB(B1EN), .OCEB(1'b1),
			.RSTA(1'b0), .RSTB(1'b0)
		);
	end else if (CFG_DBITS <= 9) begin
		DP16KD #(
			`include "bram_init_9_18_36.vh"
			.DATA_WIDTH_A(9),
			.DATA_WIDTH_B(9),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WRITEMODE_A(WRITEMODE_A),
			.WRITEMODE_B("READBEFOREWRITE"),
			.GSR("AUTO")
		) _TECHMAP_REPLACE_ (
			`include "bram_conn_9.vh"
			.CLKA(CLK2), .CLKB(CLK3),
			.WEA(|A1EN), .CEA(1'b1), .OCEA(1'b1),
			.WEB(1'b0), .CEB(B1EN), .OCEB(1'b1),
			.RSTA(1'b0), .RSTB(1'b0)
		);
	end else if (CFG_DBITS <= 18) begin
		DP16KD #(
			`include "bram_init_9_18_36.vh"
			.DATA_WIDTH_A(18),
			.DATA_WIDTH_B(18),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WRITEMODE_A(WRITEMODE_A),
			.WRITEMODE_B("READBEFOREWRITE"),
			.GSR("AUTO")
		) _TECHMAP_REPLACE_ (
			`include "bram_conn_18.vh"
			.CLKA(CLK2), .CLKB(CLK3),
			.WEA(|A1EN), .CEA(1'b1), .OCEA(1'b1),
			.WEB(1'b0), .CEB(B1EN), .OCEB(1'b1),
			.RSTA(1'b0), .RSTB(1'b0)
		);
	end else begin
		wire TECHMAP_FAIL = 1'b1;
	end endgenerate
endmodule

module \$__ECP5_PDPW16KD (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_A = 4;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [18431:0] INIT = 18432'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	input [CFG_DBITS-1:0] A1DATA;
	input [CFG_ENABLE_A-1:0] A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	output [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	localparam CLKWMUX = CLKPOL2 ? "CLKA" : "INV";
	localparam CLKRMUX = CLKPOL3 ? "CLKB" : "INV";

	PDPW16KD #(
		`include "bram_init_9_18_36.vh"
		.DATA_WIDTH_W(36),
		.DATA_WIDTH_R(36),
		.CLKWMUX(CLKWMUX),
		.CLKRMUX(CLKRMUX),
		.GSR("AUTO")
	) _TECHMAP_REPLACE_ (
		`include "bram_conn_36.vh"
		.CLKW(CLK2), .CLKR(CLK3),
		.CEW(1'b1),
		.CER(B1EN), .OCER(1'b1),
		.RST(1'b0)
	);

endmodule
