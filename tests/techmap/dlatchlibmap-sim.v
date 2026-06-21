module dffn(input CLK, D, output reg Q, output QN);

always @(negedge CLK)
	Q <= D;

assign QN = ~Q;

endmodule

module dffsr(input CLK, D, CLEAR, PRESET, output reg Q, output QN);

always @(posedge CLK, posedge CLEAR, posedge PRESET)
	if (CLEAR)
		Q <= 0;
	else if (PRESET)
		Q <= 1;
	else
		Q <= D;

assign QN = ~Q;

endmodule

module dffe(input CLK, EN, D, output reg Q, output QN);

always @(negedge CLK)
	if (EN) Q <= D;

assign QN = ~Q;

endmodule
