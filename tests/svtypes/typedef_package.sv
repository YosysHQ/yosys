package pkg;
	typedef logic [7:0] uint8_t;
endpackage

module top;

	(* keep *) (pkg::uint8_t) a = 8'hAA;

	always @* assert(a == 8'hAA);

endmodule
