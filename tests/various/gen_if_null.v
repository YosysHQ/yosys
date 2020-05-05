module test(x, y, z);
	localparam OFF = 0;
	generate
		if (OFF) ;
		else input x;
		if (!OFF) input y;
		else ;
		if (OFF) ;
		else ;
		if (OFF) ;
		input z;
	endgenerate
endmodule
