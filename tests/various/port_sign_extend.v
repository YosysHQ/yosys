module GeneratorSigned1(out);
	output wire signed out;
	assign out = 1;
endmodule

module GeneratorUnsigned1(out);
	output wire out;
	assign out = 1;
endmodule

module GeneratorSigned2(out);
	output wire signed [1:0] out;
	assign out = 2;
endmodule

module GeneratorUnsigned2(out);
	output wire [1:0] out;
	assign out = 2;
endmodule

module PassThrough(a, b);
	input wire [3:0] a;
	output wire [3:0] b;
	assign b = a;
endmodule

module act(o1, o2, o3, o4, o5, o6, o7, o8, o9, yay1, nay1, yay2, nay2);
	output wire [3:0] o1, o2, o3, o4, o5, o6, o7, o8, o9;

	// unsigned constant
	PassThrough pt1(1'b1, o1);

	// unsigned wire
	wire tmp2;
	assign tmp2 = 1'sb1;
	PassThrough pt2(tmp2, o2);

	// signed constant
	PassThrough pt3(1'sb1, o3);

	// signed wire
	wire signed tmp4;
	assign tmp4 = 1'sb1;
	PassThrough pt4(tmp4, o4);

	// signed expressions
	wire signed [1:0] tmp5a = 2'b11;
	wire signed [1:0] tmp5b = 2'b01;
	PassThrough pt5(tmp5a ^ tmp5b, o5);

	wire signed [2:0] tmp6a = 3'b100;
	wire signed [2:0] tmp6b = 3'b001;
	PassThrough pt6(tmp6a ? tmp6a : tmp6b, o6);

	wire signed [2:0] tmp7 = 3'b011;
	PassThrough pt7(~tmp7, o7);

	reg signed [2:0] tmp8 [0:0];
	initial tmp8[0] = 3'b101;
	PassThrough pt8(tmp8[0], o8);

	wire signed [2:0] tmp9a = 3'b100;
	wire signed [1:0] tmp9b = 2'b11;
	PassThrough pt9(0 ? tmp9a : tmp9b, o9);

	output wire [2:0] yay1, nay1;
	GeneratorSigned1   os1(yay1);
	GeneratorUnsigned1 ou1(nay1);

	output wire [2:0] yay2, nay2;
	GeneratorSigned2   os2(yay2);
	GeneratorUnsigned2 ou2(nay2);
endmodule

module ref(o1, o2, o3, o4, o5, o6, o7, o8, o9, yay1, nay1, yay2, nay2);
	output wire [3:0] o1, o2, o3, o4, o5, o6, o7, o8, o9;

	assign o1 = 4'b0001;
	assign o2 = 4'b0001;
	assign o3 = 4'b1111;
	assign o4 = 4'b1111;
	assign o5 = 4'b1110;
	assign o6 = 4'b1100;
	assign o7 = 4'b1100;
	assign o8 = 4'b1101;
	assign o9 = 4'b1111;

	output wire [2:0] yay1, nay1;
	assign yay1 = 3'b111;
	assign nay1 = 3'b001;

	output wire [2:0] yay2, nay2;
	assign yay2 = 3'b110;
	assign nay2 = 3'b010;
endmodule
