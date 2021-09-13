`default_nettype none

module gate(a);
	for (genvar i = 0; i < 2; i++)
		wire [i:0] x = '1;

	output wire [32:0] a;
	assign a = {1'b0, genblk1[0].x, 1'b0, genblk1[1].x, 1'b0};
endmodule

module gold(a);
	genvar i;
	for (i = 0; i < 2; i++)
		wire [i:0] x = '1;

	output wire [32:0] a;
	assign a = {1'b0, genblk1[0].x, 1'b0, genblk1[1].x, 1'b0};
endmodule
