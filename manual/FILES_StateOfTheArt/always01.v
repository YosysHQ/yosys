module uut_always01(clock, reset, c3, c2, c1, c0);

input clock, reset;
output c3, c2, c1, c0;
reg [3:0] count;

assign {c3, c2, c1, c0} = count;

always @(posedge clock)
	count <= reset ? 0 : count + 1;

endmodule
