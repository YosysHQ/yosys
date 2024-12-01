module lcu (P, G, CI, CO);
	parameter WIDTH = 2;

	input [WIDTH-1:0] P, G;
	input CI;

	output [WIDTH-1:0] CO;

	reg [WIDTH-1:0] p, g;

	\$lcu #(.WIDTH(WIDTH)) impl (.P(P), .G(G), .CI(CI), .CO(CO));

endmodule
