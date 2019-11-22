`define STRINGIFY(x) `"x`"
`define STATIC_ASSERT(x) if(!(x)) $error({"assert failed: ", `STRINGIFY(x)})

module top;

	typedef logic [1:0] uint2_t;
	typedef logic signed [3:0] int4_t;
	typedef logic signed [7:0] int8_t;
	typedef (int8_t) char_t;

	parameter (uint2_t) int2 = 2'b10;
	localparam (int4_t) int4 = -1;
	localparam (int8_t) int8 = int4;
	localparam (char_t) ch = int8;


	`STATIC_ASSERT(int2 == 2'b10);
	`STATIC_ASSERT(int4 == 4'b1111);
	`STATIC_ASSERT(int8 == 8'b11111111);
	`STATIC_ASSERT(ch   == 8'b11111111);

endmodule
