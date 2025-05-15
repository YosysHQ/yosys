
		module wide_op(
			a, b, y, c
		);
			parameter width = 1024;

			// ADD/SUB: 0/4 + (0 unsigned+unsigned, 1 unsigned+signed, 2 signed+unsigned, 3 signed+signed)
			// reserved for MUL: 8
			parameter op = 0;

			localparam ywidth = (op == 8) ? width * 2 : width;
			input[width-1:0] a;
			input[width-1:0] b;
			output [width-1:0] y;
			output c;

			generate
			if (op == 0)
				assign {c, y} = a + b;
			else if (op == 1)
				assign {c, y} = a + $signed(b);
			else if (op == 2)
				assign {c, y} = $signed(a) + b;
			else if (op == 3)
				assign {c, y} = $signed(a) + $signed(b);
			else if (op == 4)
				assign {c, y} = a - b;
			else if (op == 5)
				assign {c, y} = a - $signed(b);
			else if (op == 6)
				assign {c, y} = $signed(a) - b;
			else if (op == 7)
				assign {c, y} = $signed(a) - $signed(b);
			else if (op == 8) begin
				assign c = 0;
				assign y = a * b;
			end
			endgenerate
		endmodule
