module \$__XILINX_RAMB36_SDP72 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [8:0] A1ADDR;
	output [71:0] A1DATA;

	input [8:0] B1ADDR;
	input [71:0] B1DATA;
	input [7:0] B1EN;

	wire [15:0] A1ADDR_16 = {A1ADDR, 6'b0};
	wire [15:0] B1ADDR_16 = {B1ADDR, 6'b0};

	wire [7:0] DIP, DOP;
	wire [63:0] DI, DO;

	wire [71:0] A1DATA_BUF;
	reg [71:0] B1DATA_Q;
	reg [7:0] transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA[ 8: 0] = transparent_cycle[0] ? B1DATA_Q[ 8: 0] : A1DATA_BUF[ 8: 0];
	assign A1DATA[17: 9] = transparent_cycle[1] ? B1DATA_Q[17: 9] : A1DATA_BUF[17: 9];
	assign A1DATA[26:18] = transparent_cycle[2] ? B1DATA_Q[26:18] : A1DATA_BUF[26:18];
	assign A1DATA[35:27] = transparent_cycle[3] ? B1DATA_Q[35:27] : A1DATA_BUF[35:27];
	assign A1DATA[44:36] = transparent_cycle[4] ? B1DATA_Q[44:36] : A1DATA_BUF[44:36];
	assign A1DATA[53:45] = transparent_cycle[5] ? B1DATA_Q[53:45] : A1DATA_BUF[53:45];
	assign A1DATA[62:54] = transparent_cycle[6] ? B1DATA_Q[62:54] : A1DATA_BUF[62:54];
	assign A1DATA[71:63] = transparent_cycle[7] ? B1DATA_Q[71:63] : A1DATA_BUF[71:63];

	assign A1DATA_BUF = { DOP[7], DO[63:56], DOP[6], DO[55:48], DOP[5], DO[47:40], DOP[4], DO[39:32],
	                      DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };

	assign { DIP[7], DI[63:56], DIP[6], DI[55:48], DIP[5], DI[47:40], DIP[4], DI[39:32],
	         DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB36E1 #(
		.RAM_MODE("SDP"),
		.READ_WIDTH_A(72),
		.WRITE_WIDTH_B(72),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DOBDO(DO[63:32]),
		.DOADO(DO[31:0]),
		.DOPBDOP(DOP[7:4]),
		.DOPADOP(DOP[3:0]),
		.DIBDI(DI[63:32]),
		.DIADI(DI[31:0]),
		.DIPBDIP(DIP[7:4]),
		.DIPADIP(DIP[3:0]),

		.ADDRARDADDR(A1ADDR_16),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(4'b0),

		.ADDRBWRADDR(B1ADDR_16),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE(B1EN)
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_SDP36 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [8:0] A1ADDR;
	output [35:0] A1DATA;

	input [8:0] B1ADDR;
	input [35:0] B1DATA;
	input [3:0] B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 5'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 5'b0};

	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	wire [35:0] A1DATA_BUF;
	reg [35:0] B1DATA_Q;
	reg [3:0] transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA[ 8: 0] = transparent_cycle[0] ? B1DATA_Q[ 8: 0] : A1DATA_BUF[ 8: 0];
	assign A1DATA[17: 9] = transparent_cycle[1] ? B1DATA_Q[17: 9] : A1DATA_BUF[17: 9];
	assign A1DATA[26:18] = transparent_cycle[2] ? B1DATA_Q[26:18] : A1DATA_BUF[26:18];
	assign A1DATA[35:27] = transparent_cycle[3] ? B1DATA_Q[35:27] : A1DATA_BUF[35:27];

	assign A1DATA_BUF = { DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("SDP"),
		.READ_WIDTH_A(36),
		.WRITE_WIDTH_B(36),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DOBDO(DO[31:16]),
		.DOADO(DO[15:0]),
		.DOPBDOP(DOP[3:2]),
		.DOPADOP(DOP[1:0]),
		.DIBDI(DI[31:16]),
		.DIADI(DI[15:0]),
		.DIPBDIP(DIP[3:2]),
		.DIPADIP(DIP[1:0]),

		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE(B1EN)
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP18 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [9:0] A1ADDR;
	output [17:0] A1DATA;

	input [9:0] B1ADDR;
	input [17:0] B1DATA;
	input [1:0] B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 4'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 4'b0};

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [17:0] A1DATA_BUF;
	reg [17:0] B1DATA_Q;
	reg [1:0] transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA[ 8: 0] = transparent_cycle[0] ? B1DATA_Q[ 8: 0] : A1DATA_BUF[ 8: 0];
	assign A1DATA[17: 9] = transparent_cycle[1] ? B1DATA_Q[17: 9] : A1DATA_BUF[17: 9];

	assign A1DATA_BUF = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("TDP"),
		.READ_WIDTH_A(18),
		.READ_WIDTH_B(18),
		.WRITE_WIDTH_A(18),
		.WRITE_WIDTH_B(18),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DIADI(16'b0),
		.DIPADIP(2'b0),
		.DOADO(DO),
		.DOPADOP(DOP),
		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.DIBDI(DI),
		.DIPBDIP(DIP),
		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE({2'b00, B1EN})
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP9 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [10:0] A1ADDR;
	output [8:0] A1DATA;

	input [10:0] B1ADDR;
	input [8:0] B1DATA;
	input B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 3'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 3'b0};

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [8:0] A1DATA_BUF;
	reg [8:0] B1DATA_Q;
	reg transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA = transparent_cycle ? B1DATA_Q : A1DATA_BUF;

	assign A1DATA_BUF = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("TDP"),
		.READ_WIDTH_A(9),
		.READ_WIDTH_B(9),
		.WRITE_WIDTH_A(9),
		.WRITE_WIDTH_B(9),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DIADI(16'b0),
		.DIPADIP(2'b0),
		.DOADO(DO),
		.DOPADOP(DOP),
		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.DIBDI(DI),
		.DIPBDIP(DIP),
		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE({3'b00, B1EN})
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP4 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [11:0] A1ADDR;
	output [3:0] A1DATA;

	input [11:0] B1ADDR;
	input [3:0] B1DATA;
	input B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 2'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 2'b0};

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [3:0] A1DATA_BUF;
	reg [3:0] B1DATA_Q;
	reg transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA = transparent_cycle ? B1DATA_Q : A1DATA_BUF;

	assign A1DATA_BUF = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("TDP"),
		.READ_WIDTH_A(4),
		.READ_WIDTH_B(4),
		.WRITE_WIDTH_A(4),
		.WRITE_WIDTH_B(4),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DIADI(16'b0),
		.DIPADIP(2'b0),
		.DOADO(DO),
		.DOPADOP(DOP),
		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.DIBDI(DI),
		.DIPBDIP(DIP),
		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE({3'b00, B1EN})
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP2 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [12:0] A1ADDR;
	output [1:0] A1DATA;

	input [12:0] B1ADDR;
	input [1:0] B1DATA;
	input B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 1'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 1'b0};

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [3:0] A1DATA_BUF;
	reg [3:0] B1DATA_Q;
	reg transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA = transparent_cycle ? B1DATA_Q : A1DATA_BUF;

	assign A1DATA_BUF = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("TDP"),
		.READ_WIDTH_A(2),
		.READ_WIDTH_B(2),
		.WRITE_WIDTH_A(2),
		.WRITE_WIDTH_B(2),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DIADI(16'b0),
		.DIPADIP(2'b0),
		.DOADO(DO),
		.DOPADOP(DOP),
		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.DIBDI(DI),
		.DIPBDIP(DIP),
		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE({3'b00, B1EN})
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP1 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter TRANSP2 = 1;
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [13:0] A1ADDR;
	output A1DATA;

	input [13:0] B1ADDR;
	input B1DATA;
	input B1EN;

	wire [13:0] A1ADDR_14 = A1ADDR;
	wire [13:0] B1ADDR_14 = B1ADDR;

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [3:0] A1DATA_BUF;
	reg [3:0] B1DATA_Q;
	reg transparent_cycle;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	generate if (CLKPOL2)
		always @(posedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	else
		always @(negedge CLK2) begin transparent_cycle <= TRANSP2 && A1ADDR == B1ADDR ? B1EN : 0; B1DATA_Q <= B1DATA; end
	endgenerate

	assign A1DATA = transparent_cycle ? B1DATA_Q : A1DATA_BUF;

	assign A1DATA_BUF = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E1 #(
		.RAM_MODE("TDP"),
		.READ_WIDTH_A(1),
		.READ_WIDTH_B(1),
		.WRITE_WIDTH_A(1),
		.WRITE_WIDTH_B(1),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3)
	) _TECHMAP_REPLACE_ (
		.DIADI(16'b0),
		.DIPADIP(2'b0),
		.DOADO(DO),
		.DOPADOP(DOP),
		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.DIBDI(DI),
		.DIPBDIP(DIP),
		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.REGCEB(|0),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE({3'b00, B1EN})
	);
endmodule

