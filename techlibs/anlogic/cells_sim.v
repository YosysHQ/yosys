module AL_MAP_SEQ (
	output q,
	input ce,
	input clk,
	input sr,
	input d
);
	parameter DFFMODE = "FF"; //FF,LATCH
	parameter REGSET = "RESET"; //RESET/SET
	parameter SRMUX = "SR"; //SR/INV
	parameter SRMODE = "SYNC"; //SYNC/ASYNC
endmodule

module AL_MAP_LUT1 (
	output o,
	input a
);
	parameter [1:0] INIT = 2'h0;
	parameter EQN = "(A)";
	assign o = INIT >> a;
endmodule

module AL_MAP_LUT2 (
	output o,
	input a,
	input b
);
	parameter [3:0] INIT = 4'h0;
	parameter EQN = "(A)";
	assign o = INIT >> {b, a};
endmodule

module AL_MAP_LUT3 (
	output o,
	input a,
	input b,
	input c
);
	parameter [7:0] INIT = 8'h0;
	parameter EQN = "(A)";
	assign o = INIT >> {c, b, a};
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
	assign o = INIT >> {d, c, b, a};
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
endmodule
