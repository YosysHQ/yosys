module test(en, in, out);
input en;
input [1:0] in;
output reg [2:0] out;

always @ (en or in)
	if(en)
		out = in + 1;
endmodule		
