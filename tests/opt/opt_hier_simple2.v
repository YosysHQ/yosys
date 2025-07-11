module m(input [3:0] i, output [3:0] y);
	assign y = i + 1;
endmodule

module top(output [3:0] y);
	m inst(.i(4), .y(y));
endmodule
