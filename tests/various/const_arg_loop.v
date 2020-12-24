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
		input [4:0] var;
		input integer num;
		begin
			var[0] = var[0] ^ 1;
			operation2 = num * var;
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

// `define VERIFY
`ifdef VERIFY
    assert property (a == 2);
    assert property (A == 3);
    assert property (x1 == 16);
    assert property (x1b == 16);
    assert property (x2 == 4);
    assert property (x3 == 16);
    assert property (x4 == a << 1);
`endif
endmodule
