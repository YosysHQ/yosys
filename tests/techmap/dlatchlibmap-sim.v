module dlatchn(input ENA, D, output reg Q, output QN);

always @*
	if (~ENA)  Q <= D;

assign QN = ~Q;

endmodule

module dlatchsr(input ENA, D, CLEAR, PRESET, output reg Q, output QN);

always @*
	if      (CLEAR)   Q <= 1'b0;
	else if (PRESET)  Q <= 1'b1;
	else if (ENA)     Q <= D;

assign QN = ~Q;

endmodule
