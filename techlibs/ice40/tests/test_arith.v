module test(input [4:0] a, b, c, output [4:0] y);
	assign y = ((a+b) ^ (a-c)) - ((a*b) + (a*c) - (b*c));
endmodule
