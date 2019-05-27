module a(Q);
	output wire Q = 0;
endmodule

module b(D);
	input wire D;
endmodule

module c;
	// net definitions
	wor D;
	wand E;

	// assignments to wired logic nets
	assign D = 1;
	assign D = 0;
	assign D = 1;
	assign D = 0;

	// assignments of wired logic nets to wires
	wire F = E;

	genvar i;
	for (i = 0; i < 3; i = i + 1)
	begin : genloop
		// connection of module outputs
		a a_inst (.Q(E));

		// connection of module inputs
		b b_inst (.D(E));
	end
endmodule

