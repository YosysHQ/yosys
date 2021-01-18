`default_nettype none

module ExampleA(i, a, b);
	input wire [3:0] i;
	input wire [3:0] a;
	output wire [3:0] b;
	assign b = a;
	wire [3:0] foo = 4'd2;
	wire [3:0] bar = 4'd1;
	wire [3:0] z = i * a;
endmodule

module ExampleB(inp, out);
	parameter WIDTH = 1;
	input wire inp;
	output wire [WIDTH - 1:0] out;
	assign out[0] = inp;
	generate
		if (WIDTH > 1) begin : blk
			ExampleB #(WIDTH - 1) sub(~inp, out[WIDTH - 1:1]);
			wire [WIDTH - 2:0] sub_out;
			assign sub_out = sub.out;
		end
	endgenerate
endmodule

module gate(i1, i2, o1, o2, o3, o4, o5);
	input wire [3:0] i1, i2;
	output wire [3:0] o1, o2, o3, o4, o5;

	ExampleA ea1(i1, ea1.foo, o1);
	ExampleA ea2(i2, ea2.bar, o2);
	assign o3 = ea1.z * ea2.z;

	wire [3:0] eb1o;
	ExampleB #(4) eb1(i1[0], eb1o);
	assign o4 =
		eb1.out *
		eb1.blk.sub.out *
		eb1.blk.sub.blk.sub.out *
		eb1.blk.sub.blk.sub.blk.sub.out ;
	assign o5 =
		eb1.out *
		eb1.blk.sub_out *
		eb1.blk.sub.blk.sub_out *
		eb1.blk.sub.blk.sub.blk.sub_out ;
endmodule

module gold(i1, i2, o1, o2, o3, o4, o5);
	input wire [3:0] i1, i2;
	output wire [3:0] o1, o2, o3, o4, o5;

	ExampleA ea1(i1, 4'd2, o1);
	ExampleA ea2(i2, 4'd1, o2);
	assign o3 = i1 * 4'd2 * i2 * 4'd1;

	wire i = i1[0];
	assign o4 =
		{~i, i, ~i, i} *
		{~i, i, ~i} *
		{~i, i} *
		{~i} ;
	assign o5 = o4;
endmodule
