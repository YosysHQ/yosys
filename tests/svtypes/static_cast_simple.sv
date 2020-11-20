module top;
	wire [7:0] a, b, c, d;
	assign a = 8'd16;
	assign b = 8'd16;
	assign c = (a * b) >> 8;
	assign d = (16'(a) * b) >> 8;

	parameter P = 16;

	wire signed [7:0] s0, s1, s2;
	wire [7:0] u0, u1, u2, u3, u4, u5, u6;
	assign s0 = -8'd1;
	assign s1 = 4'(s0);
	assign s2 = 4'(unsigned'(s0));
	assign u0 = -8'd1;
	assign u1 = 4'(u0);
	assign u2 = 4'(signed'(u0));
	assign u3 = 8'(4'(s0));
	assign u4 = 8'(4'(u0));
	assign u5 = 8'(4'(signed'(-8'd1)));
	assign u6 = 8'(4'(unsigned'(-8'd1)));

	wire [8:0] n0, n1, n2, n3, n4, n5, n6, n7, n8, n9;
	assign n0 = s1;
	assign n1 = s2;
	assign n2 = 9'(s1);
	assign n3 = 9'(s2);
	assign n4 = 9'(unsigned'(s1));
	assign n5 = 9'(unsigned'(s2));
	assign n6 = 9'(u0);
	assign n7 = 9'(u1);
	assign n8 = 9'(signed'(u0));
	assign n9 = 9'(signed'(u1));

	always_comb begin
		assert(c == 8'b0000_0000);
		assert(d == 8'b0000_0001);

		assert((P + 1)'(a) == 17'b0_0000_0000_0001_0000);
		assert((P + 1)'(d - 2) == 17'b1_1111_1111_1111_1111);

		assert(s0 == 8'b1111_1111);
		assert(s1 == 8'b1111_1111);
		assert(s2 == 8'b0000_1111);
		assert(u0 == 8'b1111_1111);
		assert(u1 == 8'b0000_1111);
		assert(u2 == 8'b1111_1111);
		assert(u3 == 8'b1111_1111);
		assert(u4 == 8'b0000_1111);
		assert(u5 == 8'b1111_1111);
		assert(u6 == 8'b0000_1111);

		assert(n0 == 9'b1_1111_1111);
		assert(n1 == 9'b0_0000_1111);
		assert(n2 == 9'b1_1111_1111);
		assert(n3 == 9'b0_0000_1111);
		assert(n4 == 9'b0_1111_1111);
		assert(n5 == 9'b0_0000_1111);
		assert(n6 == 9'b0_1111_1111);
		assert(n7 == 9'b0_0000_1111);
		assert(n8 == 9'b1_1111_1111);
		assert(n9 == 9'b0_0000_1111);
	end
endmodule
