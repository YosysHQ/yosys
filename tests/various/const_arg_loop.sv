module top;
	function automatic [31:0] operation1;
		input [4:0] rounds;
		input integer num;
		integer i;
		begin
			begin : shadow
				integer rounds;
				rounds = 0;
			end
			for (i = 0; i < rounds; i = i + 1)
				num = num * 2;
			operation1 = num;
		end
	endfunction

	function automatic [31:0] pass_through;
		input [31:0] inp;
		pass_through = inp;
	endfunction

	function automatic [31:0] operation2;
		input [4:0] inp;
		input integer num;
		begin
			inp[0] = inp[0] ^ 1;
			operation2 = num * inp;
		end
	endfunction

	function automatic [31:0] operation3;
		input [4:0] rounds;
		input integer num;
		reg [4:0] rounds;
		integer i;
		begin
			begin : shadow
				integer rounds;
				rounds = 0;
			end
			for (i = 0; i < rounds; i = i + 1)
				num = num * 2;
			operation3 = num;
		end
	endfunction

	function automatic [16:0] operation4;
		input [15:0] a;
		input b;
		operation4 = {a, b};
	endfunction

	function automatic integer operation5;
		input x;
		integer x;
		operation5 = x;
	endfunction

	wire [31:0] a;
	assign a = 2;

	parameter A = 3;

	wire [31:0] x1;
	assign x1 = operation1(A, a);

	wire [31:0] x1b;
	assign x1b = operation1(pass_through(A), a);

	wire [31:0] x2;
	assign x2 = operation2(A, a);

	wire [31:0] x3;
	assign x3 = operation3(A, a);

	wire [16:0] x4;
	assign x4 = operation4(a[15:0], 0);

	wire [31:0] x5;
	assign x5 = operation5(64);

	always_comb begin
		assert(a == 2);
		assert(A == 3);
		assert(x1 == 16);
		assert(x1b == 16);
		assert(x2 == 4);
		assert(x3 == 16);
		assert(x4 == a << 1);
		assert(x5 == 64);
	end
endmodule
