package pkg;
	typedef logic [7:0] uint8_t;
	typedef enum logic [7:0] {bb=8'hBB} enum8_t;
endpackage

module top;

	(* keep *) (pkg::uint8_t) a = 8'hAA;
	(* keep *) (pkg::enum8_t) b_enum = pkg::bb;

	always @* assert(a == 8'hAA);
	always @* assert(b_enum == 8'hBB);

endmodule
