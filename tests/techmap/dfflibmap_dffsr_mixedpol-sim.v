module dffsr_mixedpol(input CLK, D, CLEAR, PRESET, output reg Q, output QN);

	always @(posedge CLK, negedge CLEAR, posedge PRESET)
		if      (PRESET)  Q <= 1'b1;
		else if (~CLEAR)  Q <= 1'b0;
		else              Q <= ~D;

	assign QN = ~Q;

endmodule
