module gate(x);
	output reg [15:0] x;
	if (1) begin : gen
		integer x;
		initial begin
			for (integer x = 5; x < 10; x++)
				if (x == 5)
					gen.x = 0;
				else
					gen.x += 2 ** x;
			x = x * 2;
		end
	end
	initial x = gen.x;
endmodule

module gold(x);
	output reg [15:0] x;
	if (1) begin : gen
		integer x;
		integer z;
		initial begin
			for (z = 5; z < 10; z++)
				if (z == 5)
					x = 0;
				else
					x += 2 ** z;
			x = x * 2;
		end
	end
	initial x = gen.x;
endmodule
