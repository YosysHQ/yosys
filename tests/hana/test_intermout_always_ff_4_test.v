module FlipFlop(clk, cs, ns);
input clk;
input [31:0] cs;
output [31:0] ns;
integer is;

always @(posedge clk)
    is <= cs;

assign ns = is;
endmodule	
