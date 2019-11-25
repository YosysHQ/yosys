module myDFF (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK)
		Q <= D;
endmodule

module myDFFE (output reg Q, input D, CLK, CE);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK) begin
		if (CE)
			Q <= D;
	end
endmodule // DFFE (positive clock edge; clock enable)


module myDFFS (output reg Q, input D, CLK, SET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(posedge CLK) begin
		if (SET)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule // DFFS (positive clock edge; synchronous set)


module myDFFSE (output reg Q, input D, CLK, CE, SET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(posedge CLK) begin
		if (SET)
			Q <= 1'b1;
		else if (CE)
			Q <= D;
end
endmodule // DFFSE (positive clock edge; synchronous set takes precedence over clock enable)


module myDFFR (output reg Q, input D, CLK, RESET);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK) begin
		if (RESET)
			Q <= 1'b0;
		else
			Q <= D;
	end
endmodule // DFFR (positive clock edge; synchronous reset)


module myDFFRE (output reg Q, input D, CLK, CE, RESET);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK) begin
		if (RESET)
			Q <= 1'b0;
		else if (CE)
			Q <= D;
	end
endmodule // DFFRE (positive clock edge; synchronous reset takes precedence over clock enable)


module myDFFP (output reg Q, input D, CLK, PRESET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(posedge CLK or posedge PRESET) begin
		if(PRESET)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule // DFFP (positive clock edge; asynchronous preset)


module myDFFPE (output reg Q, input D, CLK, CE, PRESET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(posedge CLK or posedge PRESET) begin
		if(PRESET)
			Q <= 1'b1;
		else if (CE)
			Q <= D;
	end
endmodule // DFFPE (positive clock edge; asynchronous preset; clock enable)


module myDFFC (output reg Q, input D, CLK, CLEAR);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK or posedge CLEAR) begin
		if(CLEAR)
			Q <= 1'b0;
		else
			Q <= D;
	end
endmodule // DFFC (positive clock edge; asynchronous clear)


module myDFFCE (output reg Q, input D, CLK, CE, CLEAR);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK or posedge CLEAR) begin
		if(CLEAR)
			Q <= 1'b0;
		else if (CE)
			Q <= D;
	end
endmodule // DFFCE (positive clock edge; asynchronous clear; clock enable)


module myDFFN (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK)
		Q <= D;
endmodule

module myDFFNE (output reg Q, input D, CLK, CE);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK) begin
		if (CE)
			Q <= D;
	end
endmodule // DFFNE (negative clock edge; clock enable)


module myDFFNS (output reg Q, input D, CLK, SET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(negedge CLK) begin
		if (SET)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule // DFFNS (negative clock edge; synchronous set)


module myDFFNSE (output reg Q, input D, CLK, CE, SET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(negedge CLK) begin
		if (SET)
			Q <= 1'b1;
		else if (CE)
			Q <= D;
end
endmodule // DFFNSE (negative clock edge; synchronous set takes precedence over clock enable)


module myDFFNR (output reg Q, input D, CLK, RESET);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK) begin
		if (RESET)
			Q <= 1'b0;
		else
			Q <= D;
	end
endmodule // DFFNR (negative clock edge; synchronous reset)


module myDFFNRE (output reg Q, input D, CLK, CE, RESET);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK) begin
		if (RESET)
			Q <= 1'b0;
		else if (CE)
			Q <= D;
	end
endmodule // DFFNRE (negative clock edge; synchronous reset takes precedence over clock enable)


module myDFFNP (output reg Q, input D, CLK, PRESET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(negedge CLK or posedge PRESET) begin
		if(PRESET)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule // DFFNP (negative clock edge; asynchronous preset)


module myDFFNPE (output reg Q, input D, CLK, CE, PRESET);
	parameter [0:0] INIT = 1'b1;
	initial Q = INIT;
	always @(negedge CLK or posedge PRESET) begin
		if(PRESET)
			Q <= 1'b1;
		else if (CE)
			Q <= D;
	end
endmodule // DFFNPE (negative clock edge; asynchronous preset; clock enable)


module myDFFNC (output reg Q, input D, CLK, CLEAR);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK or posedge CLEAR) begin
		if(CLEAR)
			Q <= 1'b0;
		else
			Q <= D;
	end
endmodule // DFFNC (negative clock edge; asynchronous clear)


module myDFFNCE (output reg Q, input D, CLK, CE, CLEAR);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK or posedge CLEAR) begin
		if(CLEAR)
			Q <= 1'b0;
		else if (CE)
			Q <= D;
	end
endmodule // DFFNCE (negative clock edge; asynchronous clear; clock enable)
