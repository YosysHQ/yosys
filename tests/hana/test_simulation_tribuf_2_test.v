module test(input [1:0] in, input enable, output [1:0] out);
assign out = enable ? in : 2'bzz;
endmodule
