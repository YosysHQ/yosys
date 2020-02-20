
typedef logic [3:0] outer_uint4_t;
typedef enum logic {s0, s1} outer_enum_t;

module top;

	(outer_uint4_t) u4_i = 8'hA5;
	(outer_enum_t) enum4_i = s0;
	always @(*) assert(u4_i == 4'h5);
	always @(*) assert(enum4_i == 1'b0);

	typedef logic [3:0] inner_type;
	typedef enum logic [2:0] {s2=2, s3, s4} inner_enum_t;
	(inner_type) inner_i1 = 8'h5A;
	(inner_enum_t) inner_enum1 = s3;
	always @(*) assert(inner_i1 == 4'hA);
	always @(*) assert(inner_enum1 == 3'h3);

	if (1) begin: genblock
		typedef logic [7:0] inner_type;
		parameter (inner_type) inner_const = 8'hA5;
 		typedef enum logic [2:0] {s5=5, s6, s7} inner_enum_t;
		(inner_type) inner_gb_i = inner_const; //8'hA5;
 		(inner_enum_t) inner_gb_enum1 = s7;
		always @(*) assert(inner_gb_i == 8'hA5);
 		always @(*) assert(inner_gb_enum1 == 3'h7);
	end

	(inner_type) inner_i2 = 8'h42;
	(inner_enum_t) inner_enum2 = s4;
	always @(*) assert(inner_i2 == 4'h2);
	always @(*) assert(inner_enum2 == 3'h4);


endmodule
