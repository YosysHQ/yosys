module dlatch( input d, en, output reg q );
	always @* begin
		if ( en )
			q = d;
	end
endmodule
