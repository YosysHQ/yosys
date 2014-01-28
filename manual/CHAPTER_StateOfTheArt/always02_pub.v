module uut_always02(clock,
		reset, count);

input clock, reset;
output [3:0] count;
reg [3:0] count;

always @(posedge clock) begin
	count <= count + 1;
	if (reset)
		count <= 0;
end

endmodule
