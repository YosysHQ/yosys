module top(...);

input [7:0] A;
output [7:0] B;
wire [7:0] C = 3;
assign B = A + C;

endmodule
