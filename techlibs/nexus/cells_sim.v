(* abc9_lut=1, lib_whitebox *)
module LUT4(input A, B, C, D, output Z);
	parameter INIT = "0x0000";
`include "parse_init.vh"
	localparam initp = parse_init(INIT);
	wire [7:0] s3 = D ?     initp[15:8] :    initp[7:0];
	wire [3:0] s2 = C ?       s3[ 7:4]  :       s3[3:0];
	wire [1:0] s1 = B ?       s2[ 3:2]  :       s2[1:0];
	assign Z =      A ?          s1[1]  :         s1[0];

	// Per-input delay differences are considered 'interconnect'
	// so not known yet
	specify
		(A => Z) = 233;
		(B => Z) = 233;
		(C => Z) = 233;
		(D => Z) = 233;
	endspecify

endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 5-input LUTs and is not intended to be instantiated
(* abc9_lut=2 *)
module \$__ABC9_LUT5 (input SEL, D, C, B, A, output Z);
	specify
		(SEL => Z) = 171;
		(D => Z) = 303;
		(C => Z) = 311;
		(B => Z) = 309;
		(A => Z) = 306;
	endspecify
endmodule

// Two LUT4s and MUX2
module WIDEFN9(input A0, B0, C0, D0, A1, B1, C1, D1, SEL, output Z);
	parameter INIT0 = "0x0000";
	parameter INIT1 = "0x0000";
	wire z0, z1;
	LUT4 #(.INIT(INIT0)) lut4_0 (.A(A0), .B(B0), .C(C0), .D(D0), .Z(z0));
	LUT4 #(.INIT(INIT1)) lut4_1 (.A(A1), .B(B1), .C(C1), .D(D1), .Z(z1));
	assign Z = SEL ? z1 : z0;
endmodule

(* abc9_box, lib_whitebox *)
module INV(input A, output Z);
	assign Z = !A;

	specify
		(A => Z) = 10;
	endspecify
endmodule

// Bidirectional IO buffer
module BB(input T, I, output O,
	(* iopad_external_pin *) inout B);
	assign B = T ? 1'bz : O;
	assign I = B;
endmodule

// Input buffer
module IB(
	(* iopad_external_pin *) input I,
	output O);
	assign O = I;
endmodule

// Output buffer
module OB(input I,
	(* iopad_external_pin *) output O);
	assign O = I;
endmodule

// Output buffer with tristate
module OBZ(input I, T,
	(* iopad_external_pin *) output O);
	assign O = T ? 1'bz : I;
endmodule

// Constants
module VLO(output Z);
	assign Z = 1'b0;
endmodule

module VHI(output Z);
	assign Z = 1'b1;
endmodule

// Vendor flipflops
// (all have active high clock, enable and set/reset - use INV to invert)

// Async preset
(* abc9_box, lib_whitebox *)
module FD1P3BX(input D, CK, SP, PD, output reg Q);
	parameter GSR = "DISABLED";
	initial Q = 1'b1;
	always @(posedge CK or posedge PD)
		if (PD)
			Q <= 1'b1;
		else if (SP)
			Q <= D;
	specify
		$setup(D, posedge CK, 0);
		$setup(SP, posedge CK, 212);
		$setup(PD, posedge CK, 224);
`ifndef YOSYS
		if (PD) (posedge CLK => (Q : 1)) = 0;
`else
		if (PD) (PD => Q) = 0; 	// Technically, this should be an edge sensitive path
								// but for facilitating a bypass box, let's pretend it's
								// a simple path
`endif
		if (!PD && SP) (posedge CK => (Q : D)) = 336;
	endspecify
endmodule

// Async clear
(* abc9_box, lib_whitebox *)
module FD1P3DX(input D, CK, SP, CD, output reg Q);
	parameter GSR = "DISABLED";
	initial Q = 1'b0;
	always @(posedge CK or posedge CD)
		if (CD)
			Q <= 1'b0;
		else if (SP)
			Q <= D;
	specify
		$setup(D, posedge CK, 0);
		$setup(SP, posedge CK, 212);
		$setup(CD, posedge CK, 224);
`ifndef YOSYS
		if (CD) (posedge CLK => (Q : 0)) = 0;
`else
		if (CD) (CD => Q) = 0; 	// Technically, this should be an edge sensitive path
								// but for facilitating a bypass box, let's pretend it's
								// a simple path
`endif
		if (!CD && SP) (posedge CK => (Q : D)) = 336;
	endspecify
endmodule

// Sync clear
(* abc9_flop, lib_whitebox *)
module FD1P3IX(input D, CK, SP, CD, output reg Q);
	parameter GSR = "DISABLED";
	initial Q = 1'b0;
	always @(posedge CK)
		if (CD)
			Q <= 1'b0;
		else if (SP)
			Q <= D;
	specify
		$setup(D, posedge CK, 0);
		$setup(SP, posedge CK, 212);
		$setup(CD, posedge CK, 224);
		if (!CD && SP) (posedge CK => (Q : D)) = 336;
	endspecify
endmodule

// Sync preset
(* abc9_flop, lib_whitebox *)
module FD1P3JX(input D, CK, SP, PD, output reg Q);
	parameter GSR = "DISABLED";
	initial Q = 1'b1;
	always @(posedge CK)
		if (PD)
			Q <= 1'b1;
		else if (SP)
			Q <= D;
	specify
		$setup(D, posedge CK, 0);
		$setup(SP, posedge CK, 212);
		$setup(PD, posedge CK, 224);
		if (!PD && SP) (posedge CK => (Q : D)) = 336;
	endspecify
endmodule

// LUT4 with LUT3 tap for CCU2 use only
(* lib_whitebox *)
module LUT4_3(input A, B, C, D, output Z, Z3);
	parameter INIT = "0x0000";
`include "parse_init.vh"
	localparam initp = parse_init(INIT);
	wire [7:0] s3 = D ?     initp[15:8] :     initp[7:0];
	wire [3:0] s2 = C ?        s3[ 7:4] :        s3[3:0];
	wire [1:0] s1 = B ?        s2[ 3:2] :        s2[1:0];
	assign Z =      A ?           s1[1] :          s1[0];

	wire [3:0] s2_3 = C ?   initp[ 7:4] :     initp[3:0];
	wire [1:0] s1_3 = B ?    s2_3[ 3:2] :      s2_3[1:0];
	assign Z3 =       A ?       s1_3[1] :        s1_3[0];

endmodule

// Carry primitive (incoporating two LUTs)
(* abc9_box, lib_whitebox *)
module CCU2(
	(* abc9_carry *) input CIN,
	input A1, B1, C1, D1, A0, B0, C0, D0,
	output S1, S0,
	(* abc9_carry *) output COUT);
	parameter INJECT = "YES";
	parameter INIT0 = "0x0000";
	parameter INIT1 = "0x1111";

	localparam inject_p = (INJECT == "YES") ? 1'b1 : 1'b0;

	wire LUT3_0, LUT4_0, LUT3_1, LUT4_1, carry_0;
	LUT4_3 #(.INIT(INIT0)) lut0 (.A(A0), .B(B0), .C(C0), .D(D0), .Z(LUT4_0), .Z3(LUT3_0));
	LUT4_3 #(.INIT(INIT1)) lut1 (.A(A1), .B(B1), .C(C1), .D(D1), .Z(LUT4_1), .Z3(LUT3_1));

	assign S0 = LUT4_0 ^ (CIN & ~inject_p);
	assign carry_0 = LUT4_0 ? CIN : (LUT3_0 & ~inject_p);
	assign S1 = LUT4_1 ^ (carry_0 & ~inject_p);
	assign COUT = LUT4_1 ? carry_0 : (LUT3_1 & ~inject_p);

	specify
		(A0 => S0) = 233;
		(B0 => S0) = 233;
		(C0 => S0) = 233;
		(D0 => S0) = 233;
		(CIN => S0) = 228;
		(A0 => S1) = 481;
		(B0 => S1) = 481;
		(C0 => S1) = 481;
		(D0 => S1) = 481;
		(A1 => S1) = 233;
		(B1 => S1) = 233;
		(C1 => S1) = 233;
		(D1 => S1) = 233;
		(CIN => S1) = 307;
		(A0 => COUT) = 347;
		(B0 => COUT) = 347;
		(C0 => COUT) = 347;
		(D0 => COUT) = 347;
		(A1 => COUT) = 347;
		(B1 => COUT) = 347;
		(C1 => COUT) = 347;
		(D1 => COUT) = 347;
		(CIN => COUT) = 59;
	endspecify

endmodule

// Packed flipflop
module OXIDE_FF(input CLK, LSR, CE, DI, M, output reg Q);
	parameter GSR = "ENABLED";
	parameter [127:0] CEMUX = "1";
	parameter CLKMUX = "CLK";
	parameter LSRMUX = "LSR";
	parameter REGDDR = "DISABLED";
	parameter SRMODE = "LSR_OVER_CE";
	parameter REGSET = "RESET";
	parameter [127:0] LSRMODE = "LSR";

	wire muxce;
	generate
		case (CEMUX)
			"1": assign muxce = 1'b1;
			"0": assign muxce = 1'b0;
			"INV": assign muxce = ~CE;
			default: assign muxce = CE;
		endcase
	endgenerate

	wire muxlsr = (LSRMUX == "INV") ? ~LSR : LSR;
	wire muxclk = (CLKMUX == "INV") ? ~CLK : CLK;
	wire srval;
	generate
		if (LSRMODE == "PRLD")
			assign srval = M;
		else
			assign srval = (REGSET == "SET") ? 1'b1 : 1'b0;
	endgenerate

	initial Q = srval;

	generate
		if (REGDDR == "ENABLED") begin
			if (SRMODE == "ASYNC") begin
				always @(posedge muxclk, negedge muxclk, posedge muxlsr)
					if (muxlsr)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end else begin
				always @(posedge muxclk, negedge muxclk)
					if (muxlsr)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end
		end else begin
			if (SRMODE == "ASYNC") begin
				always @(posedge muxclk, posedge muxlsr)
					if (muxlsr)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end else begin
				always @(posedge muxclk)
					if (muxlsr)
						Q <= srval;
					else if (muxce)
						Q <= DI;
			end
		end
	endgenerate
endmodule

// Packed combinational logic (for post-pnr sim)
module OXIDE_COMB(
	input A, B, C, D, // LUT inputs
	input SEL, // mux select input
	input F1, // output from LUT 1 for mux
	input FCI, // carry input
	input WAD0, WAD1, WAD2, WAD3, // LUTRAM write address inputs
	input WD, // LUTRAM write data input
	input WCK, WRE, // LUTRAM write clock and enable
	output F, // LUT/carry output
	output OFX // mux output
);
	parameter MODE = "LOGIC"; // LOGIC, CCU2, DPRAM
	parameter [15:0] INIT = 16'h0000;
	parameter INJECT = "YES";

	localparam inject_p = (INJECT == "YES") ? 1'b1 : 1'b0;

	reg [15:0] lut = INIT;

	wire [7:0] s3 = D ?     INIT[15:8] :     INIT[7:0];
	wire [3:0] s2 = C ?       s3[ 7:4] :       s3[3:0];
	wire [1:0] s1 = B ?       s2[ 3:2] :       s2[1:0];
	wire Z =        A ?          s1[1] :         s1[0];

	wire [3:0] s2_3 = C ?   INIT[ 7:4] :     INIT[3:0];
	wire [1:0] s1_3 = B ?   s2_3[ 3:2] :     s2_3[1:0];
	wire Z3 =         A ?      s1_3[1] :       s1_3[0];

	generate
		if (MODE == "DPRAM") begin
			always @(posedge WCK)
				if (WRE)
					lut[{WAD3, WAD2, WAD1, WAD0}] <= WD;
		end
		if (MODE == "CCU2") begin
			assign F = Z ^ (FCI & ~inject_p);
			assign FCO = Z ? FCI : (Z3 & ~inject_p);
		end else begin
			assign F = Z;
		end
	endgenerate

	assign OFX = SEL ? F1 : F;

endmodule

// LUTRAM
module DPR16X4(
	input [3:0] RAD, DI, WAD,
	input WRE, WCK,
	output [3:0] DO
);
	parameter INITVAL = "0x0000000000000000";
`include "parse_init.vh"
	localparam [63:0] parsed_init = parse_init_64(INITVAL);

	reg [3:0] mem[0:15];
	integer i;
	initial begin
		for (i = 0; i < 15; i++)
			mem[i] = parsed_init[i * 4 +: 4];
	end

	always @(posedge WCK)
		if (WRE)
			mem[WAD] <= DI;
	assign DO = mem[RAD];
endmodule

// Used for all the DSP models to reduce duplication
module OXIDE_DSP_REG #(
	parameter W = 18,
	parameter USED = "REGISTER",
	parameter RESETMODE = "SYNC"
) (
	input CLK, CE, RST,
	input [W-1:0] D,
	output reg [W-1:0] Q
);
	generate
		if (USED == "BYPASS")
			always @* Q = D;
		else if (USED == "REGISTER") begin
			initial Q = 0;
			if (RESETMODE == "ASYNC")
				always @(posedge CLK, posedge RST) begin
					if (RST)
						Q <= 0;
					else if (CE)
						Q <= D;
				end
			else if (RESETMODE == "SYNC")
				always @(posedge CLK) begin
					if (RST)
						Q <= 0;
					else if (CE)
						Q <= D;
				end
		end
	endgenerate
endmodule

module OXIDE_DSP_SIM #(
	// User facing parameters
	parameter REGINPUTA = "BYPASS",
	parameter REGINPUTB = "BYPASS",
	parameter REGINPUTC = "BYPASS",
	parameter REGADDSUB = "BYPASS",
	parameter REGLOADC = "BYPASS",
	parameter REGLOADC2 = "BYPASS",
	parameter REGCIN = "BYPASS",
	parameter REGPIPELINE = "BYPASS",
	parameter REGOUTPUT = "BYPASS",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC",
	// Internally used parameters
	parameter A_WIDTH = 36,
	parameter B_WIDTH = 36,
	parameter C_WIDTH = 36,
	parameter Z_WIDTH = 72,
	parameter PREADD_USED = 0,
	parameter ADDSUB_USED = 0
) (
	input [A_WIDTH-1:0] A,
	input [B_WIDTH-1:0] B,
	input [C_WIDTH-1:0] C,
	input SIGNEDA,
	input SIGNEDB,
	input SIGNEDC,
	input CIN,
	input LOADC,
	input ADDSUB,
	input CLK,
	input CEA, CEB, CEC, CEPIPE, CECTRL, CECIN, CEOUT,
	input RSTA, RSTB, RSTC, RSTPIPE, RSTCTRL, RSTCIN, RSTOUT,
	output wire [Z_WIDTH-1:0] Z
);
	
	localparam M_WIDTH = (A_WIDTH+B_WIDTH);

	/******** REGISTERS ********/

	wire [M_WIDTH-1:0] pipe_d, pipe_q;
	wire [Z_WIDTH-1:0] z_d;

	wire [A_WIDTH-1:0] a_r;
	wire [B_WIDTH-1:0] b_r;
	wire [C_WIDTH-1:0] c_r, c_r2;
	wire asgd_r, bsgd_r, csgd_r, csgd_r2;

	wire addsub_r, addsub_r2, cin_r, cin_r2, sgd_r, sgd_r2;
	wire loadc_r, loadc_r2;

	OXIDE_DSP_REG #(A_WIDTH+1, REGINPUTA, RESETMODE) a_reg(CLK, CEA, RSTA, {SIGNEDA, A}, {asgd_r, a_r});
	OXIDE_DSP_REG #(B_WIDTH+1, REGINPUTB, RESETMODE) b_reg(CLK, CEB, RSTB, {SIGNEDB, B}, {bsgd_r, b_r});
	OXIDE_DSP_REG #(C_WIDTH+1, REGINPUTC, RESETMODE) c_reg(CLK, CEC, RSTC, {SIGNEDC, C}, {csgd_r, c_r});

	OXIDE_DSP_REG #(M_WIDTH, REGPIPELINE, RESETMODE) pipe_reg(CLK, CEPIPE, RSTPIPE, pipe_d, pipe_q);

	OXIDE_DSP_REG #(2, REGADDSUB, RESETMODE) addsub_reg(CLK, CECTRL, RSTCTRL, {SIGNEDA, ADDSUB}, {sgd_r, addsub_r});
	OXIDE_DSP_REG #(1, REGLOADC, RESETMODE) loadc_reg(CLK, CECTRL, RSTCTRL, LOADC, loadc_r);
	OXIDE_DSP_REG #(2, REGPIPELINE, RESETMODE) addsub2_reg(CLK, CECTRL, RSTCTRL, {sgd_r, addsub_r}, {sgd_r2, addsub_r2});
	OXIDE_DSP_REG #(1, REGLOADC2, RESETMODE) loadc2_reg(CLK, CECTRL, RSTCTRL, loadc_r, loadc_r2);

	OXIDE_DSP_REG #(1, REGCIN, RESETMODE) cin_reg(CLK, CECIN, RSTCIN, CIN, cin_r);
	OXIDE_DSP_REG #(1, REGPIPELINE, RESETMODE) cin2_reg(CLK, CECIN, RSTCIN, cin_r, cin_r2);

	OXIDE_DSP_REG #(C_WIDTH+1, REGPIPELINE, RESETMODE) c2_reg(CLK, CEC, RSTC, {csgd_r, c_r}, {csgd_r2, c_r2});

	OXIDE_DSP_REG #(Z_WIDTH, REGOUTPUT, RESETMODE) z_reg(CLK, CEOUT, RSTOUT, z_d, Z);

	/******** PREADDER ********/

	wire [B_WIDTH-1:0] mult_b;
	wire mult_b_sgd;

	generate
		if (PREADD_USED) begin
			assign mult_b = (b_r + c_r);
			assign mult_b_sgd = (bsgd_r | csgd_r);
		end else begin
			assign mult_b = b_r;
			assign mult_b_sgd = bsgd_r;
		end
	endgenerate

	/******** MULTIPLIER ********/

	// sign extend operands if needed
	wire [M_WIDTH-1:0] mult_a_ext = {{(M_WIDTH-A_WIDTH){asgd_r ? a_r[A_WIDTH-1] : 1'b0}}, a_r};
	wire [M_WIDTH-1:0] mult_b_ext = {{(M_WIDTH-B_WIDTH){mult_b_sgd ? mult_b[B_WIDTH-1] : 1'b0}}, mult_b};

	wire [M_WIDTH-1:0] mult_m = mult_a_ext * mult_b_ext;

	/******** ACCUMULATOR ********/

	wire [Z_WIDTH-1:0] m_ext;

	generate
		if (ADDSUB_USED) begin
			assign pipe_d = mult_m;
			assign m_ext = {{(Z_WIDTH-M_WIDTH){sgd_r2 ? pipe_q[M_WIDTH-1] : 1'b0}}, pipe_q};
			assign z_d = (loadc_r2 ? c_r2 : Z) + cin_r2 + (addsub_r2 ? -m_ext : m_ext);  
		end else begin
			assign z_d = mult_m;
		end
	endgenerate


endmodule

module MULT9X9 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [8:0] A,
	input [8:0] B,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input SIGNEDA,
	input SIGNEDB,
	input RSTOUT,
	input CEOUT,
	output [17:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(9),
		.B_WIDTH(9),
		.Z_WIDTH(18),
		.PREADD_USED(0),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule

module MULT18X18 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [17:0] A,
	input [17:0] B,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input SIGNEDA,
	input SIGNEDB,
	input RSTOUT,
	input CEOUT,
	output [35:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(18),
		.B_WIDTH(18),
		.Z_WIDTH(36),
		.PREADD_USED(0),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule

module MULT18X36 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [17:0] A,
	input [35:0] B,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input SIGNEDA,
	input SIGNEDB,
	input RSTOUT,
	input CEOUT,
	output [53:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(18),
		.B_WIDTH(36),
		.Z_WIDTH(54),
		.PREADD_USED(0),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule

module MULT36X36 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [35:0] A,
	input [35:0] B,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input SIGNEDA,
	input SIGNEDB,
	input RSTOUT,
	input CEOUT,
	output [71:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(36),
		.B_WIDTH(36),
		.Z_WIDTH(72),
		.PREADD_USED(0),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule


module MULTPREADD9X9 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGINPUTC = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [8:0] A,
	input [8:0] B,
	input [8:0] C,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input CEC,
	input RSTC,
	input SIGNEDA,
	input SIGNEDB,
	input SIGNEDC,
	input RSTOUT,
	input CEOUT,
	output [17:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGINPUTC(REGINPUTC),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(9),
		.B_WIDTH(9),
		.C_WIDTH(9),
		.Z_WIDTH(18),
		.PREADD_USED(1),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B), .C(C),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.CEC(CEC), .RSTC(RSTC),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB), .SIGNEDC(SIGNEDC),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule


module MULTPREADD18X18 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGINPUTC = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [17:0] A,
	input [17:0] B,
	input [17:0] C,
	input CLK,
	input CEA,
	input RSTA,
	input CEB,
	input RSTB,
	input CEC,
	input RSTC,
	input SIGNEDA,
	input SIGNEDB,
	input SIGNEDC,
	input RSTOUT,
	input CEOUT,
	output [35:0] Z
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGINPUTC(REGINPUTC),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(18),
		.B_WIDTH(18),
		.C_WIDTH(18),
		.Z_WIDTH(36),
		.PREADD_USED(1),
		.ADDSUB_USED(0)
	) dsp_i (
		.A(A), .B(B), .C(C),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.CEC(CEC), .RSTC(RSTC),
		.SIGNEDA(SIGNEDA), .SIGNEDB(SIGNEDB), .SIGNEDC(SIGNEDC),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule


module MULTADDSUB18X18 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGINPUTC = "REGISTER",
	parameter REGADDSUB = "REGISTER",
	parameter REGLOADC = "REGISTER",
	parameter REGLOADC2 = "REGISTER",
	parameter REGCIN = "REGISTER",
	parameter REGPIPELINE = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [17:0] A,
	input [17:0] B,
	input [53:0] C,
    input CLK,
    input CEA,
    input RSTA,
    input CEB,
    input RSTB,
    input CEC,
    input RSTC,
    input SIGNED,
    input RSTPIPE,
    input CEPIPE,
    input RSTCTRL,
    input CECTRL,
    input RSTCIN,
    input CECIN,
    input LOADC,
    input ADDSUB,
    output [53:0] Z,
    input RSTOUT,
    input CEOUT,
    input CIN
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGINPUTC(REGINPUTC),
		.REGADDSUB(REGADDSUB),
		.REGLOADC(REGLOADC),
		.REGLOADC2(REGLOADC2),
		.REGCIN(REGCIN),
		.REGPIPELINE(REGPIPELINE),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(18),
		.B_WIDTH(18),
		.C_WIDTH(54),
		.Z_WIDTH(54),
		.PREADD_USED(0),
		.ADDSUB_USED(1)
	) dsp_i (
		.A(A), .B(B), .C(C),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.CEC(CEC), .RSTC(RSTC),
		.CEPIPE(CEPIPE), .RSTPIPE(RSTPIPE),
		.CECTRL(CECTRL), .RSTCTRL(RSTCTRL),
		.CECIN(CECIN), .RSTCIN(RSTCIN),
		.CIN(CIN), .LOADC(LOADC), .ADDSUB(ADDSUB),
		.SIGNEDA(SIGNED), .SIGNEDB(SIGNED), .SIGNEDC(SIGNED),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule


module MULTADDSUB36X36 #(
	parameter REGINPUTA = "REGISTER",
	parameter REGINPUTB = "REGISTER",
	parameter REGINPUTC = "REGISTER",
	parameter REGADDSUB = "REGISTER",
	parameter REGLOADC = "REGISTER",
	parameter REGLOADC2 = "REGISTER",
	parameter REGCIN = "REGISTER",
	parameter REGPIPELINE = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [35:0] A,
	input [35:0] B,
	input [107:0] C,
    input CLK,
    input CEA,
    input RSTA,
    input CEB,
    input RSTB,
    input CEC,
    input RSTC,
    input SIGNED,
    input RSTPIPE,
    input CEPIPE,
    input RSTCTRL,
    input CECTRL,
    input RSTCIN,
    input CECIN,
    input LOADC,
    input ADDSUB,
    output [107:0] Z,
    input RSTOUT,
    input CEOUT,
    input CIN
);
	OXIDE_DSP_SIM #(
		.REGINPUTA(REGINPUTA),
		.REGINPUTB(REGINPUTB),
		.REGINPUTC(REGINPUTC),
		.REGADDSUB(REGADDSUB),
		.REGLOADC(REGLOADC),
		.REGLOADC2(REGLOADC2),
		.REGCIN(REGCIN),
		.REGPIPELINE(REGPIPELINE),
		.REGOUTPUT(REGOUTPUT),
		.GSR(GSR),
		.RESETMODE(RESETMODE),

		.A_WIDTH(36),
		.B_WIDTH(36),
		.C_WIDTH(108),
		.Z_WIDTH(108),
		.PREADD_USED(0),
		.ADDSUB_USED(1)
	) dsp_i (
		.A(A), .B(B), .C(C),
		.CLK(CLK),
		.CEA(CEA), .RSTA(RSTA),
		.CEB(CEB), .RSTB(RSTB),
		.CEC(CEC), .RSTC(RSTC),
		.CEPIPE(CEPIPE), .RSTPIPE(RSTPIPE),
		.CECTRL(CECTRL), .RSTCTRL(RSTCTRL),
		.CECIN(CECIN), .RSTCIN(RSTCIN),
		.CIN(CIN), .LOADC(LOADC), .ADDSUB(ADDSUB),
		.SIGNEDA(SIGNED), .SIGNEDB(SIGNED), .SIGNEDC(SIGNED),
		.RSTOUT(RSTOUT), .CEOUT(CEOUT),
		.Z(Z)
	);
endmodule

module MULTADDSUB9X9WIDE #(
	parameter REGINPUTAB0 = "REGISTER",
	parameter REGINPUTAB1 = "REGISTER",
	parameter REGINPUTAB2 = "REGISTER",
	parameter REGINPUTAB3 = "REGISTER",
	parameter REGINPUTC = "REGISTER",
	parameter REGADDSUB = "REGISTER",
	parameter REGLOADC = "REGISTER",
	parameter REGLOADC2 = "REGISTER",
	parameter REGPIPELINE = "REGISTER",
	parameter REGOUTPUT = "REGISTER",
	parameter GSR = "ENABLED",
	parameter RESETMODE = "SYNC"
) (
	input [8:0] A0, B0, A1, B1, A2, B2, A3, B3,
	input [53:0] C,
	input CLK,
	input CEA0A1, CEA2A3,
	input RSTA0A1, RSTA2A3,
	input CEB0B1, CEB2B3,
	input RSTB0B1, RSTB2B3,
	input CEC, RSTC,
	input CECTRL, RSTCTRL,
	input SIGNED,
	input RSTPIPE, CEPIPE,
	input RSTOUT, CEOUT,
	input LOADC,
	input [3:0] ADDSUB,
	output [53:0] Z
);
	wire [17:0] m0, m1, m2, m3;

	localparam M_WIDTH = 18;
	localparam Z_WIDTH = 54;

	MULT9X9 #(
		.REGINPUTA(REGINPUTAB0), .REGINPUTB(REGINPUTAB0), .REGOUTPUT(REGPIPELINE), .GSR(GSR), .RESETMODE(RESETMODE)
	) m9_0 (
		.A(A0), .B(B0), .SIGNEDA(SIGNED), .SIGNEDB(SIGNED),
		.CLK(CLK),
		.CEA(CEA0A1), .RSTA(RSTA0A1),
		.CEB(CEB0B1), .RSTB(RSTB0B1),
		.CEOUT(CEPIPE), .RSTOUT(RSTPIPE),
		.Z(m0)
	);
	MULT9X9 #(
		.REGINPUTA(REGINPUTAB1), .REGINPUTB(REGINPUTAB1), .REGOUTPUT(REGPIPELINE), .GSR(GSR), .RESETMODE(RESETMODE)
	) m9_1 (
		.A(A1), .B(B1), .SIGNEDA(SIGNED), .SIGNEDB(SIGNED),
		.CLK(CLK),
		.CEA(CEA0A1), .RSTA(RSTA0A1),
		.CEB(CEB0B1), .RSTB(RSTB0B1),
		.CEOUT(CEPIPE), .RSTOUT(RSTPIPE),
		.Z(m1)
	);
	MULT9X9 #(
		.REGINPUTA(REGINPUTAB2), .REGINPUTB(REGINPUTAB2), .REGOUTPUT(REGPIPELINE), .GSR(GSR), .RESETMODE(RESETMODE)
	) m9_2 (
		.A(A2), .B(B2), .SIGNEDA(SIGNED), .SIGNEDB(SIGNED),
		.CLK(CLK),
		.CEA(CEA2A3), .RSTA(RSTA2A3),
		.CEB(CEB2B3), .RSTB(RSTB2B3),
		.CEOUT(CEPIPE), .RSTOUT(RSTPIPE),
		.Z(m2)
	);
	MULT9X9 #(
		.REGINPUTA(REGINPUTAB3), .REGINPUTB(REGINPUTAB3), .REGOUTPUT(REGPIPELINE), .GSR(GSR), .RESETMODE(RESETMODE)
	) m9_3 (
		.A(A3), .B(B3), .SIGNEDA(SIGNED), .SIGNEDB(SIGNED),
		.CLK(CLK),
		.CEA(CEA2A3), .RSTA(RSTA2A3),
		.CEB(CEB2B3), .RSTB(RSTB2B3),
		.CEOUT(CEPIPE), .RSTOUT(RSTPIPE),
		.Z(m3)
	);

	wire [53:0] c_r, c_r2;
	wire [3:0] addsub_r, addsub_r2;
	wire sgd_r, sgd_r2, csgd_r, csgd_r2;
	wire loadc_r, loadc_r2;

	OXIDE_DSP_REG #(5, REGADDSUB, RESETMODE) addsub_reg(CLK, CECTRL, RSTCTRL, {SIGNED, ADDSUB}, {sgd_r, addsub_r});
	OXIDE_DSP_REG #(5, REGADDSUB, RESETMODE) addsub2_reg(CLK, CECTRL, RSTCTRL, {sgd_r, addsub_r}, {sgd_r2, addsub_r2});

	OXIDE_DSP_REG #(1, REGLOADC, RESETMODE) loadc_reg(CLK, CECTRL, RSTCTRL, LOADC, loadc_r);
	OXIDE_DSP_REG #(1, REGLOADC2, RESETMODE) loadc2_reg(CLK, CECTRL, RSTCTRL, loadc_r, loadc_r2);

	OXIDE_DSP_REG #(55, REGINPUTC, RESETMODE) c_reg(CLK, CEC, RSTC, {SIGNED, C}, {csgd_r, c_r});
	OXIDE_DSP_REG #(55, REGPIPELINE, RESETMODE) c2_reg(CLK, CEC, RSTC, {csgd_r, c_r}, {csgd_r2, c_r2});


	wire [18:0] m0_ext, m1_ext, m2_ext, m3_ext;

	assign m0_ext = {sgd_r2 ? m0[M_WIDTH-1] : 1'b0, m0};
	assign m1_ext = {sgd_r2 ? m1[M_WIDTH-1] : 1'b0, m1};
	assign m2_ext = {sgd_r2 ? m2[M_WIDTH-1] : 1'b0, m2};
	assign m3_ext = {sgd_r2 ? m3[M_WIDTH-1] : 1'b0, m3};

	wire [18:0] s0 = addsub_r2[2] ? (m0_ext - m1_ext) : (m0_ext + m1_ext);
	wire [18:0] s1 = addsub_r2[3] ? (m2_ext - m3_ext) : (m2_ext + m3_ext);

	wire [53:0] s0_ext = {{(54-19){sgd_r2 ? s0[18] : 1'b0}}, s0};
	wire [53:0] s1_ext = {{(54-19){sgd_r2 ? s1[18] : 1'b0}}, s1};

	wire [53:0] c_op = loadc_r2 ? c_r2 : Z;

	// The diagram in the docs is wrong! It is not two cascaded 2-input add/subs as shown,
	// but a three-input unit with negation controls on two inputs (i.e. addsub_r2[0]
	// negates s1 not (s1 +/- s0))
	wire [53:0] z_d =  c_op + (addsub_r2[0] ? -s1_ext : s1_ext) + (addsub_r2[1] ? -s0_ext : s0_ext);

	OXIDE_DSP_REG #(Z_WIDTH, REGOUTPUT, RESETMODE) z_reg(CLK, CEOUT, RSTOUT, z_d, Z);

endmodule
