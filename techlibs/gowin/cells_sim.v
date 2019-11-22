module LUT1(output F, input I0);
	parameter [1:0] INIT = 0;
	assign F = I0 ? INIT[1] : INIT[0];
endmodule

module LUT2(output F, input I0, I1);
	parameter [3:0] INIT = 0;
	wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module LUT3(output F, input I0, I1, I2);
	parameter [7:0] INIT = 0;
	wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module LUT4(output F, input I0, I1, I2, I3);
	parameter [15:0] INIT = 0;
	wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
	wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module MUX2 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;
  assign O = S0 ? I1 : I0;
endmodule

module MUX2_LUT5 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;
  MUX2 mux2_lut5 (O, I0, I1, S0);
endmodule

module MUX2_LUT6 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;
  MUX2 mux2_lut6 (O, I0, I1, S0);
endmodule

module MUX2_LUT7 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;
  MUX2 mux2_lut7 (O, I0, I1, S0);
endmodule

module MUX2_LUT8 (O, I0, I1, S0);
  input I0,I1;
  input S0;
  output O;
  MUX2 mux2_lut8 (O, I0, I1, S0);
endmodule

module DFF (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK)
		Q <= D;
endmodule

module DFFE (output reg Q, input D, CLK, CE);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) begin
    if (CE)
      Q <= D;
  end
endmodule // DFFE (positive clock edge; clock enable)


module DFFS (output reg Q, input D, CLK, SET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else
      Q <= D;	
  end
endmodule // DFFS (positive clock edge; synchronous set)


module DFFSE (output reg Q, input D, CLK, CE, SET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
end
endmodule // DFFSE (positive clock edge; synchronous set takes precedence over clock enable)


module DFFR (output reg Q, input D, CLK, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFR (positive clock edge; synchronous reset)


module DFFRE (output reg Q, input D, CLK, CE, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFRE (positive clock edge; synchronous reset takes precedence over clock enable)


module DFFP (output reg Q, input D, CLK, PRESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else
      Q <= D;
  end
endmodule // DFFP (positive clock edge; asynchronous preset)


module DFFPE (output reg Q, input D, CLK, CE, PRESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
  end
endmodule // DFFPE (positive clock edge; asynchronous preset; clock enable)


module DFFC (output reg Q, input D, CLK, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFC (positive clock edge; asynchronous clear)


module DFFCE (output reg Q, input D, CLK, CE, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFCE (positive clock edge; asynchronous clear; clock enable)


module DFFN (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK)
		Q <= D;
endmodule

module DFFNE (output reg Q, input D, CLK, CE);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK) begin
    if (CE)
      Q <= D;
  end
endmodule // DFFNE (negative clock edge; clock enable)


module DFFNS (output reg Q, input D, CLK, SET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else
      Q <= D;	
  end
endmodule // DFFNS (negative clock edge; synchronous set)


module DFFNSE (output reg Q, input D, CLK, CE, SET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK) begin
    if (SET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
end
endmodule // DFFNSE (negative clock edge; synchronous set takes precedence over clock enable)


module DFFNR (output reg Q, input D, CLK, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFNR (negative clock edge; synchronous reset)


module DFFNRE (output reg Q, input D, CLK, CE, RESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK) begin
    if (RESET)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNRE (negative clock edge; synchronous reset takes precedence over clock enable)


module DFFNP (output reg Q, input D, CLK, PRESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else
      Q <= D;
  end
endmodule // DFFNP (negative clock edge; asynchronous preset)


module DFFNPE (output reg Q, input D, CLK, CE, PRESET);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK or posedge PRESET) begin
    if(PRESET)
      Q <= 1'b1;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNPE (negative clock edge; asynchronous preset; clock enable)


module DFFNC (output reg Q, input D, CLK, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else
      Q <= D;
  end
endmodule // DFFNC (negative clock edge; asynchronous clear)


module DFFNCE (output reg Q, input D, CLK, CE, CLEAR);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge CLK or posedge CLEAR) begin
    if(CLEAR)
      Q <= 1'b0;
    else if (CE)
      Q <= D;
  end
endmodule // DFFNCE (negative clock edge; asynchronous clear; clock enable)

// TODO add more DFF sim cells

module VCC(output V);
	assign V = 1;
endmodule

module GND(output G);
	assign G = 0;
endmodule

module IBUF(output O, input I);
	assign O = I;
endmodule

module OBUF(output O, input I);
	assign O = I;
endmodule

module TBUF (O, I, OEN);
  input I, OEN;
  output O;
  assign O = OEN ? I : 1'bz;
endmodule

module IOBUF (O, IO, I, OEN);
  input I,OEN;
  output O;
  inout IO;
  assign IO = OEN ? I : 1'bz;
  assign I = IO;
endmodule

module GSR (input GSRI);
	wire GSRO = GSRI;
endmodule

module ALU (SUM, COUT, I0, I1, I3, CIN);

input I0;
input I1;
input I3;
input CIN;
output SUM;
output COUT;

localparam ADD = 0;
localparam SUB = 1;
localparam ADDSUB = 2;
localparam NE = 3;
localparam GE = 4;
localparam LE = 5;
localparam CUP = 6;
localparam CDN = 7;
localparam CUPCDN = 8;
localparam MULT = 9;

parameter ALU_MODE = 0;

reg S, C;

assign SUM = S ^ CIN;
assign COUT = S? CIN : C;

always @* begin
	case (ALU_MODE)
		ADD: begin
			S = I0 ^ I1;
			C = I0;
		end
		SUB: begin
			S = I0 ^ ~I1;
			C = I0;
		end
		ADDSUB: begin
			S = I3? I0 ^ I1 : I0 ^ ~I1;
			C = I0;
		end
		NE: begin
			S = I0 ^ ~I1;
			C = 1'b1;
		end
		GE: begin
			S = I0 ^ ~I1;
			C = I0;
		end
		LE: begin
			S = ~I0 ^ I1;
			C = I1;
		end
		CUP: begin
			S = I0;
			C = 1'b0;
		end
		CDN: begin
			S = ~I0;
			C = 1'b1;
		end
		CUPCDN: begin
			S = I3? I0 : ~I0;
			C = I0;
		end
		MULT: begin
			S = I0 & I1;
			C = I0 & I1;
		end
	endcase
end

endmodule


module RAM16S4 (DO, DI, AD, WRE, CLK);
   parameter WIDTH  = 4;
   parameter INIT_0 = 16'h0000;
   parameter INIT_1 = 16'h0000;
   parameter INIT_2 = 16'h0000;
   parameter INIT_3 = 16'h0000;
   
   input  [WIDTH-1:0] AD;
   input  [WIDTH-1:0] DI;
   output [WIDTH-1:0] DO;
   input 	      CLK;
   input 	      WRE;

   reg [15:0] 	    mem0, mem1, mem2, mem3;
   
   initial begin
      mem0 = INIT_0;
      mem1 = INIT_1;
      mem2 = INIT_2;
      mem3 = INIT_3;	
   end
   
   assign	DO[0] = mem0[AD];
   assign	DO[1] = mem1[AD];
   assign	DO[2] = mem2[AD];
   assign	DO[3] = mem3[AD];
   
   always @(posedge CLK) begin
      if (WRE) begin
	 mem0[AD] <= DI[0];
	 mem1[AD] <= DI[1];
	 mem2[AD] <= DI[2];
	 mem3[AD] <= DI[3];
      end
   end
   
endmodule // RAM16S4


(* blackbox *)
module SDP (DO, DI, BLKSEL, ADA, ADB, WREA, WREB, CLKA, CLKB, CEA, CEB, OCE, RESETA, RESETB);
//1'b0: Bypass mode; 1'b1 Pipeline mode
parameter READ_MODE = 1'b0;
parameter BIT_WIDTH_0 = 32; // 1, 2, 4, 8, 16, 32
parameter BIT_WIDTH_1 = 32; // 1, 2, 4, 8, 16, 32
parameter BLK_SEL = 3'b000;
parameter RESET_MODE = "SYNC";
parameter INIT_RAM_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_08 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_09 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_0F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_10 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_11 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_12 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_13 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_14 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_15 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_16 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_17 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_18 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_19 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_1F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_20 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_21 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_22 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_23 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_24 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_25 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_26 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_27 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_28 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_29 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_2F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_30 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_31 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_32 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_33 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_34 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_35 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_36 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_37 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_38 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_39 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
parameter INIT_RAM_3F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

input CLKA, CEA, CLKB, CEB;
input OCE; // clock enable of memory output register
input RESETA, RESETB; // resets output registers, not memory contents
input WREA, WREB; // 1'b0: read enabled; 1'b1: write enabled
input [13:0] ADA, ADB;
input [31:0] DI;
input [2:0] BLKSEL;
output [31:0] DO;

endmodule

