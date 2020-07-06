
typedef logic [3:0] outer_uint4_t;

module top;

	(outer_uint4_t) u4_i = 8'hA5;
	always @(*) assert(u4_i == 4'h5);

	typedef logic [3:0] inner_type;
	(inner_type) inner_i1 = 8'h5A;
	always @(*) assert(inner_i1 == 4'hA);

	if (1) begin: genblock
		typedef logic [7:0] inner_type;
		(inner_type) inner_gb_i = 8'hA5;
		always @(*) assert(inner_gb_i == 8'hA5);
	end

	(inner_type) inner_i2 = 8'h42;
	always @(*) assert(inner_i2 == 4'h2);


endmodule
