module top;

	assert property ($countbits(15'b011xxxxzzzzzzzz, '0            ) ==  1);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '1            ) ==  2);
	assert property ($countbits(15'b011xxxxzzzzzzzz, 'x            ) ==  4);
	assert property ($countbits(15'b011xxxxzzzzzzzz, 'z            ) ==  8);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '0, '1        ) ==  3);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '1, '1, '0    ) ==  3);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '0, 'x        ) ==  5);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '0, 'z        ) ==  9);
	assert property ($countbits(15'bz1x10xzxzzxzzzz, '0, 'z        ) ==  9);
	assert property ($countbits(15'b011xxxxzzzzzzzz, 'x, 'z        ) == 12);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '1, 'z        ) == 10);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '1, 'x, 'z    ) == 14);
	assert property ($countbits(15'b011xxxxzzzzzzzz, '1, 'x, 'z, '0) == 15);

	assert property ($countbits(0,      '0) == 32); // test integers
	assert property ($countbits(0,      '1) ==  0);
	assert property ($countbits(80'b0,  '0) == 80); // test something bigger than integer
	assert property ($countbits(80'bx0, 'x) == 79);

	always_comb begin
		logic       one;
		logic [1:0] two;
		logic [3:0] four;

		// Make sure that the width of the whole expression doesn't affect the width of the shift
		// operations inside the function.
		one  = $countbits(3'b100, '1) & 1'b1;
		two  = $countbits(3'b111, '1) & 2'b11;
		four = $countbits(3'b111, '1) & 4'b1111;

		assert (one  == 1);
		assert (two  == 3);
		assert (four == 3);
	end

	assert property ($countones(8'h00) == 0);
	assert property ($countones(8'hff) == 8);
	assert property ($countones(8'ha5) == 4);
	assert property ($countones(8'h13) == 3);

	logic       test1 = 1'b1;
	logic [4:0] test5 = 5'b10101;

	assert property ($countones(test1) == 1);
	assert property ($countones(test5) == 3);

	assert property ($isunknown(8'h00) == 0);
	assert property ($isunknown(8'hff) == 0);
	assert property ($isunknown(8'hx0) == 1);
	assert property ($isunknown(8'h1z) == 1);
	assert property ($isunknown(8'hxz) == 1);

	assert property ($onehot(8'h00) == 0);
	assert property ($onehot(8'hff) == 0);
	assert property ($onehot(8'h01) == 1);
	assert property ($onehot(8'h80) == 1);
	assert property ($onehot(8'h81) == 0);
	assert property ($onehot(8'h20) == 1);

	assert property ($onehot0(8'h00) == 1);
	assert property ($onehot0(8'hff) == 0);
	assert property ($onehot0(8'h01) == 1);
	assert property ($onehot0(8'h80) == 1);
	assert property ($onehot0(8'h81) == 0);
	assert property ($onehot0(8'h20) == 1);

endmodule
