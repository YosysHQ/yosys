// LUT RAMs for Virtex 5, Virtex 6, Spartan 6, Series 7, Ultrascale.
// The definitions are in lutrams_xc5v.txt.


module $__ANALOGDEVICES_LUTRAM_SP_ (...);

parameter INIT = 0;
parameter OPTION_ABITS = 5;
parameter WIDTH = 8;
parameter BITS_USED = 0;

output [WIDTH-1:0] PORT_RW_RD_DATA;
input [WIDTH-1:0] PORT_RW_WR_DATA;
input [OPTION_ABITS-1:0] PORT_RW_ADDR;
input PORT_RW_WR_EN;
input PORT_RW_CLK;

function [(1 << OPTION_ABITS)-1:0] init_slice;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice[i] = INIT[i * WIDTH + idx];
endfunction

function [(2 << OPTION_ABITS)-1:0] init_slice2;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice2[2 * i +: 2] = INIT[i * WIDTH + idx * 2 +: 2];
endfunction

generate
case(OPTION_ABITS)
5: if (WIDTH == 8)
	RAM32M
	#(
		.INIT_D(init_slice2(0)),
		.INIT_C(init_slice2(1)),
		.INIT_B(init_slice2(2)),
		.INIT_A(init_slice2(3)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_RW_RD_DATA[7:6]),
		.DOB(PORT_RW_RD_DATA[5:4]),
		.DOC(PORT_RW_RD_DATA[3:2]),
		.DOD(PORT_RW_RD_DATA[1:0]),
		.DIA(PORT_RW_WR_DATA[7:6]),
		.DIB(PORT_RW_WR_DATA[5:4]),
		.DIC(PORT_RW_WR_DATA[3:2]),
		.DID(PORT_RW_WR_DATA[1:0]),
		.ADDRA(PORT_RW_ADDR),
		.ADDRB(PORT_RW_ADDR),
		.ADDRC(PORT_RW_ADDR),
		.ADDRD(PORT_RW_ADDR),
		.WE(PORT_RW_WR_EN),
		.WCLK(PORT_RW_CLK),
	);
else
	RAM32M16
	#(
		.INIT_H(init_slice2(0)),
		.INIT_G(init_slice2(1)),
		.INIT_F(init_slice2(2)),
		.INIT_E(init_slice2(3)),
		.INIT_D(init_slice2(4)),
		.INIT_C(init_slice2(5)),
		.INIT_B(init_slice2(6)),
		.INIT_A(init_slice2(7)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_RW_RD_DATA[15:14]),
		.DOB(PORT_RW_RD_DATA[13:12]),
		.DOC(PORT_RW_RD_DATA[11:10]),
		.DOD(PORT_RW_RD_DATA[9:8]),
		.DOE(PORT_RW_RD_DATA[7:6]),
		.DOF(PORT_RW_RD_DATA[5:4]),
		.DOG(PORT_RW_RD_DATA[3:2]),
		.DOH(PORT_RW_RD_DATA[1:0]),
		.DIA(PORT_RW_WR_DATA[15:14]),
		.DIB(PORT_RW_WR_DATA[13:12]),
		.DIC(PORT_RW_WR_DATA[11:10]),
		.DID(PORT_RW_WR_DATA[9:8]),
		.DIE(PORT_RW_WR_DATA[7:6]),
		.DIF(PORT_RW_WR_DATA[5:4]),
		.DIG(PORT_RW_WR_DATA[3:2]),
		.DIH(PORT_RW_WR_DATA[1:0]),
		.ADDRA(PORT_RW_ADDR),
		.ADDRB(PORT_RW_ADDR),
		.ADDRC(PORT_RW_ADDR),
		.ADDRD(PORT_RW_ADDR),
		.ADDRE(PORT_RW_ADDR),
		.ADDRF(PORT_RW_ADDR),
		.ADDRG(PORT_RW_ADDR),
		.ADDRH(PORT_RW_ADDR),
		.WE(PORT_RW_WR_EN),
		.WCLK(PORT_RW_CLK),
	);
6: begin
	genvar i;
	for (i = 0; i < WIDTH; i = i + 1)
		if (BITS_USED[i])
			RAM64X1S
			#(
				.INIT(init_slice(i)),
			)
			slice
			(
				.A0(PORT_RW_ADDR[0]),
				.A1(PORT_RW_ADDR[1]),
				.A2(PORT_RW_ADDR[2]),
				.A3(PORT_RW_ADDR[3]),
				.A4(PORT_RW_ADDR[4]),
				.A5(PORT_RW_ADDR[5]),
				.D(PORT_RW_WR_DATA[i]),
				.O(PORT_RW_RD_DATA[i]),
				.WE(PORT_RW_WR_EN),
				.WCLK(PORT_RW_CLK),
			);
end
default:
	$error("invalid OPTION_ABITS/WIDTH combination");
endcase
endgenerate

endmodule


module $__ANALOGDEVICES_LUTRAM_DP_ (...);

parameter INIT = 0;
parameter OPTION_ABITS = 5;
parameter WIDTH = 4;
parameter BITS_USED = 0;

output [WIDTH-1:0] PORT_RW_RD_DATA;
input [WIDTH-1:0] PORT_RW_WR_DATA;
input [OPTION_ABITS-1:0] PORT_RW_ADDR;
input PORT_RW_WR_EN;
input PORT_RW_CLK;

output [WIDTH-1:0] PORT_R_RD_DATA;
input [OPTION_ABITS-1:0] PORT_R_ADDR;

function [(1 << OPTION_ABITS)-1:0] init_slice;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice[i] = INIT[i * WIDTH + idx];
endfunction

function [(2 << OPTION_ABITS)-1:0] init_slice2;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice2[2 * i +: 2] = INIT[i * WIDTH + idx * 2 +: 2];
endfunction

generate
case (OPTION_ABITS)
5: if (WIDTH == 4)
	RAM32M
	#(
		.INIT_D(init_slice2(0)),
		.INIT_C(init_slice2(0)),
		.INIT_B(init_slice2(1)),
		.INIT_A(init_slice2(1)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[3:2]),
		.DOB(PORT_RW_RD_DATA[3:2]),
		.DOC(PORT_R_RD_DATA[1:0]),
		.DOD(PORT_RW_RD_DATA[1:0]),
		.DIA(PORT_RW_WR_DATA[3:2]),
		.DIB(PORT_RW_WR_DATA[3:2]),
		.DIC(PORT_RW_WR_DATA[1:0]),
		.DID(PORT_RW_WR_DATA[1:0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_RW_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_RW_ADDR),
		.WE(PORT_RW_WR_EN),
		.WCLK(PORT_RW_CLK),
	);
else
	RAM32M16
	#(
		.INIT_H(init_slice2(0)),
		.INIT_G(init_slice2(0)),
		.INIT_F(init_slice2(1)),
		.INIT_E(init_slice2(1)),
		.INIT_D(init_slice2(2)),
		.INIT_C(init_slice2(2)),
		.INIT_B(init_slice2(3)),
		.INIT_A(init_slice2(3)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[7:6]),
		.DOB(PORT_RW_RD_DATA[7:6]),
		.DOC(PORT_R_RD_DATA[5:4]),
		.DOD(PORT_RW_RD_DATA[5:4]),
		.DOE(PORT_R_RD_DATA[3:2]),
		.DOF(PORT_RW_RD_DATA[3:2]),
		.DOG(PORT_R_RD_DATA[1:0]),
		.DOH(PORT_RW_RD_DATA[1:0]),
		.DIA(PORT_RW_WR_DATA[7:6]),
		.DIB(PORT_RW_WR_DATA[7:6]),
		.DIC(PORT_RW_WR_DATA[5:4]),
		.DID(PORT_RW_WR_DATA[5:4]),
		.DIE(PORT_RW_WR_DATA[3:2]),
		.DIF(PORT_RW_WR_DATA[3:2]),
		.DIG(PORT_RW_WR_DATA[1:0]),
		.DIH(PORT_RW_WR_DATA[1:0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_RW_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_RW_ADDR),
		.ADDRE(PORT_R_ADDR),
		.ADDRF(PORT_RW_ADDR),
		.ADDRG(PORT_R_ADDR),
		.ADDRH(PORT_RW_ADDR),
		.WE(PORT_RW_WR_EN),
		.WCLK(PORT_RW_CLK),
	);
6: begin
	genvar i;
	for (i = 0; i < WIDTH; i = i + 1)
		if (BITS_USED[i])
			RAM64X1D
			#(
				.INIT(init_slice(i)),
			)
			slice
			(
				.A0(PORT_RW_ADDR[0]),
				.A1(PORT_RW_ADDR[1]),
				.A2(PORT_RW_ADDR[2]),
				.A3(PORT_RW_ADDR[3]),
				.A4(PORT_RW_ADDR[4]),
				.A5(PORT_RW_ADDR[5]),
				.D(PORT_RW_WR_DATA[i]),
				.SPO(PORT_RW_RD_DATA[i]),
				.WE(PORT_RW_WR_EN),
				.WCLK(PORT_RW_CLK),
				.DPRA0(PORT_R_ADDR[0]),
				.DPRA1(PORT_R_ADDR[1]),
				.DPRA2(PORT_R_ADDR[2]),
				.DPRA3(PORT_R_ADDR[3]),
				.DPRA4(PORT_R_ADDR[4]),
				.DPRA5(PORT_R_ADDR[5]),
				.DPO(PORT_R_RD_DATA[i]),
			);
end
7: begin
	genvar i;
	for (i = 0; i < WIDTH; i = i + 1)
		if (BITS_USED[i])
			RAM128X1D
			#(
				.INIT(init_slice(i)),
			)
			slice
			(
				.A(PORT_RW_ADDR),
				.D(PORT_RW_WR_DATA[i]),
				.SPO(PORT_RW_RD_DATA[i]),
				.WE(PORT_RW_WR_EN),
				.WCLK(PORT_RW_CLK),
				.DPRA(PORT_R_ADDR),
				.DPO(PORT_R_RD_DATA[i]),
			);
end
8: begin
	genvar i;
	for (i = 0; i < WIDTH; i = i + 1)
		if (BITS_USED[i])
			RAM256X1D
			#(
				.INIT(init_slice(i)),
			)
			slice
			(
				.A(PORT_RW_ADDR),
				.D(PORT_RW_WR_DATA[i]),
				.SPO(PORT_RW_RD_DATA[i]),
				.WE(PORT_RW_WR_EN),
				.WCLK(PORT_RW_CLK),
				.DPRA(PORT_R_ADDR),
				.DPO(PORT_R_RD_DATA[i]),
			);
end
default:
	$error("invalid OPTION_ABITS/WIDTH combination");
endcase
endgenerate

endmodule


module $__ANALOGDEVICES_LUTRAM_SDP_ (...);

parameter INIT = 0;
parameter OPTION_ABITS = 5;
parameter WIDTH = 6;
parameter BITS_USED = 0;

input [WIDTH-1:0] PORT_W_WR_DATA;
input [OPTION_ABITS-1:0] PORT_W_ADDR;
input PORT_W_WR_EN;
input PORT_W_CLK;

output [WIDTH-1:0] PORT_R_RD_DATA;
input [OPTION_ABITS-1:0] PORT_R_ADDR;

function [(1 << OPTION_ABITS)-1:0] init_slice;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice[i] = INIT[i * WIDTH + idx];
endfunction

function [(2 << OPTION_ABITS)-1:0] init_slice2;
	input integer idx;
	integer i;
	for (i = 0; i < (1 << OPTION_ABITS); i = i + 1)
		init_slice2[2 * i +: 2] = INIT[i * WIDTH + idx * 2 +: 2];
endfunction

generate
case (OPTION_ABITS)
5: if (WIDTH == 6)
	RAM32M
	#(
		.INIT_C(init_slice2(0)),
		.INIT_B(init_slice2(1)),
		.INIT_A(init_slice2(2)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[5:4]),
		.DOB(PORT_R_RD_DATA[3:2]),
		.DOC(PORT_R_RD_DATA[1:0]),
		.DIA(PORT_W_WR_DATA[5:4]),
		.DIB(PORT_W_WR_DATA[3:2]),
		.DIC(PORT_W_WR_DATA[1:0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_R_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_W_ADDR),
		.WE(PORT_W_WR_EN),
		.WCLK(PORT_W_CLK),
	);
else
	RAM32M16
	#(
		.INIT_G(init_slice2(0)),
		.INIT_F(init_slice2(1)),
		.INIT_E(init_slice2(2)),
		.INIT_D(init_slice2(3)),
		.INIT_C(init_slice2(4)),
		.INIT_B(init_slice2(5)),
		.INIT_A(init_slice2(6)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[13:12]),
		.DOB(PORT_R_RD_DATA[11:10]),
		.DOC(PORT_R_RD_DATA[9:8]),
		.DOD(PORT_R_RD_DATA[7:6]),
		.DOE(PORT_R_RD_DATA[5:4]),
		.DOF(PORT_R_RD_DATA[3:2]),
		.DOG(PORT_R_RD_DATA[1:0]),
		.DIA(PORT_W_WR_DATA[13:12]),
		.DIB(PORT_W_WR_DATA[11:10]),
		.DIC(PORT_W_WR_DATA[9:8]),
		.DID(PORT_W_WR_DATA[7:6]),
		.DIE(PORT_W_WR_DATA[5:4]),
		.DIF(PORT_W_WR_DATA[3:2]),
		.DIG(PORT_W_WR_DATA[1:0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_R_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_R_ADDR),
		.ADDRE(PORT_R_ADDR),
		.ADDRF(PORT_R_ADDR),
		.ADDRG(PORT_R_ADDR),
		.ADDRH(PORT_W_ADDR),
		.WE(PORT_W_WR_EN),
		.WCLK(PORT_W_CLK),
	);
6: if (WIDTH == 3)
	RAM64M
	#(
		.INIT_C(init_slice(0)),
		.INIT_B(init_slice(1)),
		.INIT_A(init_slice(2)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[2]),
		.DOB(PORT_R_RD_DATA[1]),
		.DOC(PORT_R_RD_DATA[0]),
		.DIA(PORT_W_WR_DATA[2]),
		.DIB(PORT_W_WR_DATA[1]),
		.DIC(PORT_W_WR_DATA[0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_R_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_W_ADDR),
		.WE(PORT_W_WR_EN),
		.WCLK(PORT_W_CLK),
	);
else
	RAM64M8
	#(
		.INIT_G(init_slice(0)),
		.INIT_F(init_slice(1)),
		.INIT_E(init_slice(2)),
		.INIT_D(init_slice(3)),
		.INIT_C(init_slice(4)),
		.INIT_B(init_slice(5)),
		.INIT_A(init_slice(6)),
	)
	_TECHMAP_REPLACE_
	(
		.DOA(PORT_R_RD_DATA[6]),
		.DOB(PORT_R_RD_DATA[5]),
		.DOC(PORT_R_RD_DATA[4]),
		.DOD(PORT_R_RD_DATA[3]),
		.DOE(PORT_R_RD_DATA[2]),
		.DOF(PORT_R_RD_DATA[1]),
		.DOG(PORT_R_RD_DATA[0]),
		.DIA(PORT_W_WR_DATA[6]),
		.DIB(PORT_W_WR_DATA[5]),
		.DIC(PORT_W_WR_DATA[4]),
		.DID(PORT_W_WR_DATA[3]),
		.DIE(PORT_W_WR_DATA[2]),
		.DIF(PORT_W_WR_DATA[1]),
		.DIG(PORT_W_WR_DATA[0]),
		.ADDRA(PORT_R_ADDR),
		.ADDRB(PORT_R_ADDR),
		.ADDRC(PORT_R_ADDR),
		.ADDRD(PORT_R_ADDR),
		.ADDRE(PORT_R_ADDR),
		.ADDRF(PORT_R_ADDR),
		.ADDRG(PORT_R_ADDR),
		.ADDRH(PORT_W_ADDR),
		.WE(PORT_W_WR_EN),
		.WCLK(PORT_W_CLK),
	);
default:
	$error("invalid OPTION_ABITS/WIDTH combination");
endcase
endgenerate

endmodule
