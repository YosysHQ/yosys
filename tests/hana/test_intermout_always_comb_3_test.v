module test (in1, in2, out);
input  in1, in2;
output  reg out;

always @ ( in1 or in2)
	if(in1 > in2)
		out = in1;
	else
		out = in2;
endmodule		
