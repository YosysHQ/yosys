package pkg;
	typedef logic [7:0] uint8_t;
	typedef enum logic [7:0] {bb=8'hBB, cc=8'hCC} enum8_t;

	localparam uint8_t PCONST = cc;
	parameter uint8_t PCONST_COPY = PCONST;
endpackage

module top;

	(* keep *) pkg::uint8_t a = 8'hAA;
	(* keep *) pkg::enum8_t b_enum = pkg::bb;

	always_comb assert(a == 8'hAA);
	always_comb assert(b_enum == 8'hBB);
	always_comb assert(pkg::PCONST == pkg::cc);
	always_comb assert(pkg::PCONST_COPY == pkg::cc);

endmodule
