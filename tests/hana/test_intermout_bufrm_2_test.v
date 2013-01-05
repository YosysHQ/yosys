module test(input in, output out);
//intermediate buffers should be removed
wire w1, w2;
assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule
