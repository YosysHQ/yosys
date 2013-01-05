module FlipFlop(clk, cs, ns);
input clk;
input [7:0] cs;
output [7:0] ns;
integer is;

always @(posedge clk)
    is <= cs;

assign ns = is;
endmodule	
