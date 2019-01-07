// Like flow.v, but results in a network identical to Figure 2(b).
module top(...);
	input a,b,c,d,e,f;
	wire A = b&c;
	wire B = c|d;
	wire C = e&f;
	wire D = A|B;
	wire E = a&D;
	wire F = D&C;
	wire G = F|B;
	wire H = a&F;
	wire I = E|G;
	wire J = G&C;
	output p = H&I;
	output q = A|J;
endmodule
