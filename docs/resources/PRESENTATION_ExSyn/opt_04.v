module test(input CLK, ARST,
            output [7:0] Q1, Q2, Q3);

wire NO_CLK = 0;

always @(posedge CLK, posedge ARST)
	if (ARST)
		Q1 <= 42;

always @(posedge NO_CLK, posedge ARST)
	if (ARST)
		Q2 <= 42;
	else
		Q2 <= 23;

always @(posedge CLK)
	Q3 <= 42;

endmodule
