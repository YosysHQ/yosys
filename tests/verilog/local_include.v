`include "temp_foo.v"
module top (input x, output y);
	foo bar (.a(x), .b(y));
endmodule
