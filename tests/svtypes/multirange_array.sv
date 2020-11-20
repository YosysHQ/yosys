// test for multirange arrays

`define STRINGIFY(x) `"x`"
`define STATIC_ASSERT(x) if(!(x)) $error({"assert failed: ", `STRINGIFY(x)})

module top;

	logic a [3];
	logic b [3][5];
	logic c [3][5][7];

	`STATIC_ASSERT($bits(a) == 3);
	`STATIC_ASSERT($bits(b) == 15);
	`STATIC_ASSERT($bits(c) == 105);

endmodule
