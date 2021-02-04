module top;
	parameter YES = 1;
	generate
		if (YES) wire y;
		else wire n;

		if (!YES) wire n;
		else wire y;

		case (YES)
			1: wire y;
			0: wire n;
		endcase

		case (!YES)
			0: wire y;
			1: wire n;
		endcase

		if (YES) wire y;
		else wire n;

		if (!YES) wire n;
		else wire y;
	endgenerate
endmodule
