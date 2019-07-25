module example(
	input wire CLK,
	output wire [7:0] LED
);

reg [27:0] ctr;
initial ctr = 0;

always @(posedge CLK)
	ctr <= ctr + 1;

assign LED = ctr[27:20];

endmodule
