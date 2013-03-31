module uut_always03(clock, in1, in2, in3, in4, in5, in6, in7, out1, out2, out3);

input clock, in1, in2, in3, in4, in5, in6, in7;
output out1, out2, out3;
reg out1, out2, out3;

always @(posedge clock) begin
	out1 = in1;
	if (in2)
		out1 = !out1;
	out2 <= out1;
	if (in3)
		out2 <= out2;
	if (in4)
		if (in5)
			out3 <= in6;
		else
			out3 <= in7;
	out1 = out1 ^ out2;
end

endmodule
