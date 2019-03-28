// Exact reproduction of Figure 2(a) from 10.1109/43.273754.
module top(...);
	input a,b,c,d,e,f;
	wire nA = b&c;
	wire A = !nA;
	wire nB = c|d;
	wire B = !nB;
	wire nC = e&f;
	wire C = !nC;
	wire D = A|B;
	wire E = a&D;
	wire nF = D&C;
	wire F = !nF;
	wire nG = F|B;
	wire G = !nG;
	wire H = a&F;
	wire I = E|G;
	wire J = G&C;
	wire np = H&I;
	output p = !np;
	output q = A|J;
endmodule
