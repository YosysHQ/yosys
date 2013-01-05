module test(input [7:0] IN, input [3:0] SHIFT, output [7:0] OUT);

assign OUT = IN << SHIFT;
endmodule
