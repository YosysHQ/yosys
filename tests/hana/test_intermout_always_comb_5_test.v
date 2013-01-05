module test(ctrl, in1,  in2, out);
input ctrl;
input  in1, in2;
output  reg out;

always @ (ctrl or in1 or in2)
	if(ctrl)
		out = in1 & in2;
	else 
		out = in1 | in2;
endmodule		
