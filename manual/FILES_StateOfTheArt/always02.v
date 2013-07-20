module uut_always02(clock, reset, c3, c2, c1, c0);

input clock, reset;
output c3, c2, c1, c0;
reg [3:0] count;

assign {c3, c2, c1, c0} = count;

always @(posedge clock) begin
	count <= count + 1;
	if (reset)
		count <= 0;
end

endmodule
