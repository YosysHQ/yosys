module adlatch( input d, rst, en, output reg q );
	always @* begin
		if (rst)
			q = 0;
		else if (en)
			q = d;
	end
endmodule
