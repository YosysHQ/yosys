`default_nettype none
module test;
	localparam OFF = 0;
	generate
		if (OFF) ;
		else wire x;
		if (!OFF) wire y;
		else ;
		if (OFF) ;
		else ;
		if (OFF) ;
		wire z;
	endgenerate
	assign genblk1.x = 0;
	assign genblk2.y = 0;
	assign z = 0;
endmodule
