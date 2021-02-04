module top(z);
	output integer z;
	initial begin
		integer x;
		x = 1;
		begin
			integer y;
			y = x + 1;
			begin
				integer z;
				z = y + 1;
				y = z + 1;
			end
			z = y + 1;
		end
	end
endmodule
