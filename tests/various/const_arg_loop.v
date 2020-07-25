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

	function automatic [31:0] operation2;
		input [4:0] var;
		input integer num;
		begin
			var[0] = var[0] ^ 1;
			operation2 = num * var;
		end
	endfunction

	wire [31:0] a;
	assign a = 2;

	parameter A = 3;

	wire [31:0] x1;
	assign x1 = operation1(A, a);

	wire [31:0] x2;
	assign x2 = operation2(A, a);

// `define VERIFY
`ifdef VERIFY
    assert property (a == 2);
    assert property (A == 3);
    assert property (x1 == 16);
    assert property (x2 == 4);
`endif
endmodule
