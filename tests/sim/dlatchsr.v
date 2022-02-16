module dlatchsr( input d, set, clr, en, output reg q );
	always @* begin
		if ( clr )
			q = 0;
		else if (set)
			q = 1;
		else
			if (en)
				q = d;
	end
endmodule
