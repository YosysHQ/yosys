module test(input  [3:0] A, B,
            output [3:0] Y, Z);
assign Y = A + B, Z = B + A;
endmodule
