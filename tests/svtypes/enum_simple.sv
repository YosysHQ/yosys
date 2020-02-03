
module enum_simple(input clk, input rst);

	enum {s0, s1, s2, s3} test_enum;
	typedef enum logic [1:0] {
		ts0, ts1, ts2, ts3
	} states_t;
	(states_t) state;
	(states_t) enum_const = ts1;

	always @(posedge clk) begin
		if (rst) begin
			test_enum <= s3;
			state <= ts0;
		end else begin
			//test_enum
			if (test_enum == s0)
				test_enum <= s1;
			else if (test_enum == s1)
				test_enum <= s2;
			else if (test_enum == s2)
				test_enum <= s3;
			else if (test_enum == s3)
				test_enum <= s0;
			else
				assert(1'b0); //should be unreachable

			//state
			if (state == ts0)
				state <= ts1;
			else if (state == ts1)
				state <= ts2;
			else if (state == ts2)
				state <= ts0;
			else
				assert(1'b0); //should be unreachable
		end
	end

	always @(*) begin
		assert(state != 2'h3);
		assert(s0 == '0);
		assert(ts0 == '0);
		assert(enum_const == ts1);
	end

endmodule
