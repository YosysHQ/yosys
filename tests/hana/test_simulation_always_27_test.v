module FlipFlop(clock, cs, ns);
input clock;
input cs;
output reg ns;
reg temp;

always @(posedge clock)
begin
    temp <= cs;
	ns <= temp;
end	

endmodule	
