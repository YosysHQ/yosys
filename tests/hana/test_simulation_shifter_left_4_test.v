module test(input [3:0] IN, input [2:0] SHIFT, output [3:0] OUT);

assign OUT = IN << SHIFT;
endmodule
