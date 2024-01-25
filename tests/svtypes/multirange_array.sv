// test for multirange arrays

`define STRINGIFY(x) `"x`"
`define STATIC_ASSERT(x) if(!(x)) $error({"assert failed: ", `STRINGIFY(x)})

module top;

	logic a [3];
	logic b [3][5];
	logic c [3][5][7];
	logic [2:0] d;
	logic [2:0][4:0] e;
	logic [2:0][4:0][6:0] f;
	logic [2:0] g [3];
	logic [2:0][4:0] h [3][5];
	logic [2:0][4:0][6:0] i [3][5][7];

	`STATIC_ASSERT($bits(a) == 3);
	`STATIC_ASSERT($bits(b) == 15);
	`STATIC_ASSERT($bits(c) == 105);
	`STATIC_ASSERT($bits(d) == 3);
	`STATIC_ASSERT($bits(e) == 15);
	`STATIC_ASSERT($bits(f) == 105);
	`STATIC_ASSERT($bits(g) == 9);
	`STATIC_ASSERT($bits(h) == 225);
	`STATIC_ASSERT($bits(i) == 11025);

endmodule
