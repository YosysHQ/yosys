// Exact reproduction of Figure 3(a) from 10.1109/92.285741.
module top(...);
	input a,b,c,d,e,f,g,h;
	wire x = !(c|d);
	wire y = !(e&f);
	wire u = !(a&b);
	wire v = !(x|y);
	wire w = !(g&h);
	output s = !(u|v);
	output t = !(v|w);
endmodule
