module test(input A, B, output Y);
assign Y = A ? A ? B : 1'b1 : B;
endmodule
