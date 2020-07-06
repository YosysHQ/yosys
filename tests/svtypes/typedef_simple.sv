module top;

	typedef logic [1:0] uint2_t;
	typedef logic signed [3:0] int4_t;
	typedef logic signed [7:0] int8_t;
	typedef (int8_t) char_t;

	(* keep *) (uint2_t) int2 = 2'b10;
	(* keep *) (int4_t) int4 = -1;
	(* keep *) (int8_t) int8 = int4;
	(* keep *) (char_t) ch = int8;


	always @* assert(int2 == 2'b10);
	always @* assert(int4 == 4'b1111);
	always @* assert(int8 == 8'b11111111);
	always @* assert(ch   == 8'b11111111);

endmodule
