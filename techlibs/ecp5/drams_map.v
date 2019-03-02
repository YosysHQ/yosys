module \$__TRELLIS_DPR16X4 (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [63:0] INIT = 64'bx;
	parameter CLKPOL2 = 1;
	input CLK1;

	input [3:0] A1ADDR;
	output [3:0] A1DATA;

	input [3:0] B1ADDR;
	input [3:0] B1DATA;
	input B1EN;

	localparam WCKMUX = CLKPOL2 ? "WCK" : "INV";

	TRELLIS_DPR16X4 #(
		.INITVAL(INIT),
		.WCKMUX(WCKMUX),
		.WREMUX("WRE")
	) _TECHMAP_REPLACE_ (
		.RAD(A1ADDR),
		.DO(A1DATA),

		.WAD(B1ADDR),
		.DI(B1DATA),
		.WCK(CLK1),
		.WRE(B1EN)
	);
endmodule

module \$__TRELLIS_DPR16X4_REG (CLK1, CLK2, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter [63:0] INIT = 64'bx;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter TRANSP2 = 0;

	input CLK1, CLK2;

	input [3:0] A1ADDR;
	output [3:0] A1DATA;
	input A1EN;

	input [3:0] B1ADDR;
	input [3:0] B1DATA;
	input B1EN;

	localparam WCKMUX = CLKPOL2 ? "WCK" : "INV";

	wire [3:0] raddr, rdata;
	wire [1023:0] _TECHMAP_DO_PROC = "proc";

	TRELLIS_DPR16X4 #(
		.INITVAL(INIT),
		.WCKMUX(WCKMUX),
		.WREMUX("WRE")
	) _TECHMAP_REPLACE_ (
		.RAD(raddr),
		.DO(rdata),

		.WAD(B1ADDR),
		.DI(B1DATA),
		.WCK(CLK1),
		.WRE(B1EN)
	);

	generate
		if (TRANSP2) begin
			reg [3:0] raddr_reg;
			if (CLKPOL2) begin
				always @(posedge CLK2) if(A1EN) raddr_reg <= A1ADDR;
			end else begin
				always @(negedge CLK2) if(A1EN) raddr_reg <= A1ADDR;
			end
			assign A1DATA = rdata;
			assign raddr = raddr_reg;
		end else begin
			reg [3:0] rdata_reg;
			if (CLKPOL2) begin
				always @(posedge CLK2) if(A1EN) rdata_reg <= rdata;
			end else begin
				always @(negedge CLK2) if(A1EN) rdata_reg <= rdata;
			end
			assign A1DATA = rdata_reg;
			assign raddr = A1ADDR;
		end
	endgenerate
endmodule
