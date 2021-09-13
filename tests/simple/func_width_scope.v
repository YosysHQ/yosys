module top(inp, out1, out2);
	input wire signed inp;

	localparam WIDTH_A = 5;
	function automatic [WIDTH_A-1:0] func1;
		input reg [WIDTH_A-1:0] inp;
		func1 = ~inp;
	endfunction
	wire [func1(0)-1:0] xc;
	assign xc = 1'sb1;
	wire [WIDTH_A-1:0] xn;
	assign xn = func1(inp);

	generate
		if (1) begin : blk
			localparam WIDTH_A = 6;
			function automatic [WIDTH_A-1:0] func2;
				input reg [WIDTH_A-1:0] inp;
				func2 = ~inp;
			endfunction
			wire [func2(0)-1:0] yc;
			assign yc = 1'sb1;
			wire [WIDTH_A-1:0] yn;
			assign yn = func2(inp);

			localparam WIDTH_B = 7;
			function automatic [WIDTH_B-1:0] func3;
				input reg [WIDTH_B-1:0] inp;
				func3 = ~inp;
			endfunction
			wire [func3(0)-1:0] zc;
			assign zc = 1'sb1;
			wire [WIDTH_B-1:0] zn;
			assign zn = func3(inp);
		end
	endgenerate

	output wire [1023:0] out1, out2;
	assign out1 = {xc, 1'b0, blk.yc, 1'b0, blk.zc};
	assign out2 = {xn, 1'b0, blk.yn, 1'b0, blk.zn};
endmodule
