// Like pack1.v, but results in a simpler network.
module top(...);
	input a,b,c,d,e,f,g,h;
	wire x = c|d;
	wire y = e&f;
	wire u = a&b;
	wire v = x|y;
	wire w = g&h;
	output s = u|v;
	output t = v|w;
endmodule
