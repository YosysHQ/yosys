`define TEST(kwd) \
	kwd kwd``_1; \
	kwd kwd``_2; \
	initial kwd``_1 = 1; \
	assign kwd``_2 = 1;

`define TEST_VAR(kwd) \
	var kwd var_``kwd``_1; \
	var kwd var_``kwd``_2; \
	initial var_``kwd``_1 = 1; \
	assign var_``kwd``_2 = 1;

`define TEST_WIRE(kwd) \
	wire kwd wire_``kwd``_1; \
	wire kwd wire_``kwd``_2; \
	initial wire_``kwd``_1 = 1; \
	assign wire_``kwd``_2 = 1;

module top;

`TEST(wire) // wire assigned in a block
`TEST(reg) // reg assigned in a continuous assignment
`TEST(logic)
`TEST(integer)

`TEST_VAR(reg) // reg assigned in a continuous assignment
`TEST_VAR(logic)
`TEST_VAR(integer)

`TEST_WIRE(logic) // wire assigned in a block
`TEST_WIRE(integer) // wire assigned in a block

endmodule
