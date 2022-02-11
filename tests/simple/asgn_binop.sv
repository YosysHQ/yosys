`define TEST(name, asgnop)\
	module test_``name ( \
		input logic [3:0] a, b, \
		output logic [3:0] c \
	); \
		always @* begin \
			c = a; \
			c asgnop b; \
		end \
	endmodule

`TEST(add, +=)
`TEST(sub, -=)
`TEST(mul, *=)
`TEST(div, /=)
`TEST(mod, %=)
`TEST(bit_and, &=)
`TEST(bit_or , |=)
`TEST(bit_xor, ^=)
`TEST(shl, <<=)
`TEST(shr, >>=)
`TEST(sshl, <<<=)
`TEST(sshr, >>>=)
