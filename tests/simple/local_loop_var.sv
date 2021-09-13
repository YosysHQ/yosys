module top(out);
	output integer out;
	initial begin
		integer i;
		for (i = 0; i < 5; i = i + 1)
			if (i == 0)
				out = 1;
			else
				out += 2 ** i;
	end
endmodule
