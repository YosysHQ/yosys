module test(input [63:0] IN, input [6:0] SHIFT, output [63:0] OUT);

assign OUT = IN << SHIFT;
endmodule
