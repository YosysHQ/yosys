module AL_MAP_SEQ (
	output reg q,
	input ce,
	input clk,
	input sr,
	input d
);
	parameter DFFMODE = "FF"; //FF,LATCH
	parameter REGSET = "RESET"; //RESET/SET
	parameter SRMUX = "SR"; //SR/INV
	parameter SRMODE = "SYNC"; //SYNC/ASYNC

	wire clk_ce;
	assign clk_ce = ce ? clk : 1'b0;

	wire srmux;
	generate
		case (SRMUX)
			"SR": assign srmux = sr;
			"INV": assign srmux = ~sr;
			default: assign srmux = sr;
		endcase
	endgenerate	

	wire regset;
	generate
		case (REGSET)
			"RESET": assign regset = 1'b0;
			"SET": assign regset = 1'b1;
			default: assign regset = 1'b0;
		endcase
	endgenerate

	initial q = regset;

	generate
   		if (DFFMODE == "FF") 
		begin
			if (SRMODE == "ASYNC") 
			begin
				always @(posedge clk_ce, posedge srmux)
					if (srmux)
						q <= regset;
					else 
						q <= d;	
			end 
			else
			begin
				always @(posedge clk_ce)
					if (srmux)
						q <= regset;
					else 
						q <= d;	
			end
		end
		else
		begin
			// DFFMODE == "LATCH"
			if (SRMODE == "ASYNC") 
			begin
				always @(clk_ce, srmux)
					if (srmux)
						q <= regset;
					else 
						q <= d;	
			end 
			else
			begin
				always @(clk_ce)
					if (srmux)
						q <= regset;
					else 
						q <= d;	
			end
		end
    endgenerate
endmodule

module AL_MAP_LUT1 (
	output o,
	input a
);
	parameter [1:0] INIT = 2'h0;
	parameter EQN = "(A)";

	assign o = a ? INIT[1] : INIT[0];	
endmodule

module AL_MAP_LUT2 (
	output o,
	input a,
	input b
);
	parameter [3:0] INIT = 4'h0;
	parameter EQN = "(A)";

	wire [1:0] s1 = b ? INIT[ 3:2] : INIT[1:0];
	assign o = a ? s1[1] : s1[0];	
endmodule

module AL_MAP_LUT3 (
	output o,
	input a,
	input b,
	input c
);
	parameter [7:0] INIT = 8'h0;
	parameter EQN = "(A)";

	wire [3:0] s2 = c ? INIT[ 7:4] : INIT[3:0];
	wire [1:0] s1 = b ?   s2[ 3:2] :   s2[1:0];
	assign o = a ? s1[1] : s1[0];	
endmodule

module AL_MAP_LUT4 (
	output o,
	input a,
	input b,
	input c,
	input d
);
	parameter [15:0] INIT = 16'h0;
	parameter EQN = "(A)";

	wire [7:0] s3 = d ? INIT[15:8] : INIT[7:0];
	wire [3:0] s2 = c ?   s3[ 7:4] :   s3[3:0];
	wire [1:0] s1 = b ?   s2[ 3:2] :   s2[1:0];
	assign o = a ? s1[1] : s1[0];	
endmodule

module AL_MAP_LUT5 (
	output o,
	input a,
	input b,
	input c,
	input d,
	input e
);
	parameter [31:0] INIT = 32'h0;
	parameter EQN = "(A)";
	assign o = INIT >> {e, d, c, b, a};
endmodule


module AL_MAP_LUT6 (
	output o,
	input a,
	input b,
	input c,
	input d,
	input e,
	input f
);
	parameter [63:0] INIT = 64'h0;
	parameter EQN = "(A)";
	assign o = INIT >> {f, e, d, c, b, a};
endmodule

module AL_MAP_ALU2B (
   input cin,
   input a0, b0, c0, d0,
   input a1, b1, c1, d1,
   output s0, s1, cout
);
	parameter [15:0] INIT0 = 16'h0000;
	parameter [15:0] INIT1 = 16'h0000;
	parameter FUNC0 = "NO";
	parameter FUNC1 = "NO";
endmodule

module AL_MAP_ADDER (
  input a,
  input b,
  input c,
  output [1:0] o
);
	parameter ALUTYPE = "ADD";

	generate
		case (ALUTYPE)
			"ADD": 		 assign o = a + b + c;
			"SUB": 		 assign o = a - b - c;
			"A_LE_B":    assign o = a - b - c;

			"ADD_CARRY":    assign o = {  a, 1'b0 };
			"SUB_CARRY":    assign o = { ~a, 1'b0 };
			"A_LE_B_CARRY": assign o = {  a, 1'b0 };
			default: assign o = a + b + c;
		endcase
	endgenerate	

endmodule
