// Simple exists-forall demo

module demo8;
	wire [7:0] prime = $anyconst;
	wire [3:0] factor = $allconst;

	always @* begin
		if (1 < factor && factor < prime)
			assume((prime % factor) != 0);
		assume(prime > 1);
	end
endmodule
