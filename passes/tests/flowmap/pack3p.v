// Like pack2.v, but results in a simpler network.
module top(...);
	input a,b,c,d,e,f,g,h,i,j;
	wire x = a&b;
	wire y = c|d;
	wire z = e|f;
	wire n0 = g&h;
	wire n1 = i|j;
	wire w = x&y;
	wire n2 = z&n0;
	wire n3 = n0|n1;
	wire n4 = n2|n3;
	wire v = w|n5;
	output u = w&v;
endmodule
