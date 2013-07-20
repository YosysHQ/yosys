module uut(in1, in2, in3, out1, out2);

input [8:0] in1, in2, in3;
output [8:0] out1, out2;

assign out1 = in1 + in2 + (in3 >> 4);

endmodule
