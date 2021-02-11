module top(
	input wire [3:0] inp,
	output wire [3:0] out1, out2, out3, out4, out5,
	output reg [3:0] out6
);
	function automatic [3:0] flip;
		input [3:0] inp;
		flip = ~inp;
	endfunction

	function automatic [3:0] help;
		input [3:0] inp;
		help = flip(inp);
	endfunction

	// while loops are const-eval-only
	function automatic [3:0] loop;
		input [3:0] inp;
		reg [3:0] val;
		begin
			val = inp;
			loop = 1;
			while (val != inp) begin
				loop = loop * 2;
				val = val + 1;
			end
		end
	endfunction

	// not const-eval-only, despite calling a const-eval-only function
	function automatic [3:0] help_mul;
		input [3:0] inp;
		help_mul = inp * loop(2);
	endfunction

	// can be elaborated so long as exp is a constant
	function automatic [3:0] pow_flip_a;
		input [3:0] base, exp;
		begin
			pow_flip_a = 1;
			if (exp > 0)
				pow_flip_a = base * pow_flip_a(flip(base), exp - 1);
		end
	endfunction

	function automatic [3:0] pow_flip_b;
		input [3:0] base, exp;
		begin
			out6[exp] = base & 1;
			pow_flip_b = 1;
			if (exp > 0)
				pow_flip_b = base * pow_flip_b(flip(base), exp - 1);
		end
	endfunction

	assign out1 = flip(flip(inp));
	assign out2 = help(flip(inp));
	assign out3 = help_mul(inp);
	assign out4 = pow_flip_a(flip(inp), 3);
	assign out5 = pow_flip_b(2, 2);
endmodule
