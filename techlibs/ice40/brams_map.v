
module \$__ICE40_RAM4K_M0 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [0:0] CLKPOL2 = 1;
	parameter [0:0] CLKPOL3 = 1;

	input CLK2;
	input CLK3;

	input [7:0] A1ADDR;
	output [15:0] A1DATA;

	input [7:0] B1ADDR;
	input [15:0] B1DATA;
	input [15:0] B1EN;

	wire [10:0] A1ADDR_11 = A1ADDR;
	wire [10:0] B1ADDR_11 = B1ADDR;

	generate
		case ({CLKPOL2, CLKPOL3})
			2'b00:
				SB_RAM40_4KNRNW #(.WRITE_MODE(0), .READ_MODE(0)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA), .RADDR(A1ADDR_11),               .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA), .WADDR(B1ADDR_11), .MASK(~B1EN), .WCLK(CLK3), .WCLKE(1'b1), .WE(|B1EN)
				);
			2'b01:
				SB_RAM40_4KNR #(.WRITE_MODE(0), .READ_MODE(0)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA), .RADDR(A1ADDR_11),               .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA), .WADDR(B1ADDR_11), .MASK(~B1EN), .WCLK(CLK3), .WCLKE(1'b1), .WE(|B1EN)
				);
			2'b10:
				SB_RAM40_4KNW #(.WRITE_MODE(0), .READ_MODE(0)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA), .RADDR(A1ADDR_11),               .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA), .WADDR(B1ADDR_11), .MASK(~B1EN), .WCLK(CLK3), .WCLKE(1'b1), .WE(|B1EN)
				);
			2'b11:
				SB_RAM40_4K #(.WRITE_MODE(0), .READ_MODE(0)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA), .RADDR(A1ADDR_11),               .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA), .WADDR(B1ADDR_11), .MASK(~B1EN), .WCLK(CLK3), .WCLKE(1'b1), .WE(|B1EN)
				);
		endcase
	endgenerate
endmodule

module \$__ICE40_RAM4K_M123 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 8;

	parameter [0:0] CLKPOL2 = 1;
	parameter [0:0] CLKPOL3 = 1;

	localparam MODE =
		CFG_ABITS ==  9 ? 1 :
		CFG_ABITS == 10 ? 2 :
		CFG_ABITS == 11 ? 3 : 'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	wire [10:0] A1ADDR_11 = A1ADDR;
	wire [10:0] B1ADDR_11 = B1ADDR;

	wire [15:0] A1DATA_16, B1DATA_16;

	generate
		if (MODE == 1) begin
			assign A1DATA = {A1DATA_16[14], A1DATA_16[12], A1DATA_16[10], A1DATA_16[ 8],
			                 A1DATA_16[ 6], A1DATA_16[ 4], A1DATA_16[ 2], A1DATA_16[ 0]};
			assign B1DATA_16 = {B1DATA[7], B1DATA[7], B1DATA[6], B1DATA[6], B1DATA[5], B1DATA[5], B1DATA[4], B1DATA[4],
			                    B1DATA[3], B1DATA[3], B1DATA[2], B1DATA[2], B1DATA[1], B1DATA[1], B1DATA[0], B1DATA[0]};
		end
		if (MODE == 2) begin
			assign A1DATA = {A1DATA_16[13], A1DATA_16[9], A1DATA_16[5], A1DATA_16[1]};
			assign B1DATA_16 = {B1DATA[3], B1DATA[3], B1DATA[3], B1DATA[3], B1DATA[2], B1DATA[2], B1DATA[2], B1DATA[2],
			                    B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0]};
		end
		if (MODE == 3) begin
			assign A1DATA = {A1DATA_16[11], A1DATA_16[3]};
			assign B1DATA_16 = {B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1], B1DATA[1],
			                    B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0], B1DATA[0]};
		end
	endgenerate

	generate
		case ({CLKPOL2, CLKPOL3})
			2'b00:
				SB_RAM40_4KNRNW #(.WRITE_MODE(MODE), .READ_MODE(MODE)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA_16), .RADDR(A1ADDR_11), .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA_16), .WADDR(B1ADDR_11), .WCLK(CLK3), .WCLKE(1'b1), .WE(B1EN)
				);
			2'b01:
				SB_RAM40_4KNR #(.WRITE_MODE(MODE), .READ_MODE(MODE)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA_16), .RADDR(A1ADDR_11), .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA_16), .WADDR(B1ADDR_11), .WCLK(CLK3), .WCLKE(1'b1), .WE(B1EN)
				);
			2'b10:
				SB_RAM40_4RNW #(.WRITE_MODE(MODE), .READ_MODE(MODE)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA_16), .RADDR(A1ADDR_11), .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA_16), .WADDR(B1ADDR_11), .WCLK(CLK3), .WCLKE(1'b1), .WE(B1EN)
				);
			2'b11:
				SB_RAM40_4K #(.WRITE_MODE(MODE), .READ_MODE(MODE)) _TECHMAP_REPLACE_ (
					.RDATA(A1DATA_16), .RADDR(A1ADDR_11), .RCLK(CLK2), .RCLKE(1'b1), .RE(1'b1),
					.WDATA(B1DATA_16), .WADDR(B1ADDR_11), .WCLK(CLK3), .WCLKE(1'b1), .WE(B1EN)
				);
		endcase
	endgenerate
endmodule

