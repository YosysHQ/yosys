module FlipFlop(clock, cs, ns);
input clock;
input [3:0] cs;
output reg [3:0] ns;
reg [3:0] temp;

always @(posedge clock)
begin
    temp = cs;
	ns = temp;
end	

endmodule	
