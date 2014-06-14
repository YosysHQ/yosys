
module demo_001(y1, y2, y3, y4);
	output [7:0] y1, y2, y3, y4;

	localparam [7:0] p1 = 123.45;
	localparam real p2 = 123.45;
	localparam real p3 = 123;
	localparam p4 = 123.45;

	assign y1 = p1 + 0.2;
	assign y2 = p2 + 0.2;
	assign y3 = p3 + 0.2;
	assign y4 = p4 + 0.2;
endmodule

module demo_002(s, a, y);
	input [4:0] s;
	input [3:0] a;
	output [7:0] y;

	reg [7:0] data [21*16-1:0];
	integer i;

	initial begin
		for (i = 0; i < 16; i = i+1) begin
			data[ 0*16 + i] = 128 + 64 * $ln    (i*0.2 - 0.8);
			data[ 1*16 + i] = 128 + 64 * $log10 (i*0.2 - 0.8);
			data[ 2*16 + i] = 128 + 64 * $exp   (i*0.2 - 0.8);
			data[ 3*16 + i] = 128 + 64 * $sqrt  (i*0.2 - 0.8);
			data[ 4*16 + i] = 128 + 64 * $floor (i*0.2 - 0.8);
			data[ 5*16 + i] = 128 + 64 * $ceil  (i*0.2 - 0.8);
			data[ 6*16 + i] = 128 + 64 * $sin   (i*0.2 - 0.8);
			data[ 7*16 + i] = 128 + 64 * $cos   (i*0.2 - 0.8);
			data[ 8*16 + i] = 128 + 64 * $tan   (i*0.2 - 0.8);
			data[ 9*16 + i] = 128 + 64 * $asin  (i*0.2 - 0.8);
			data[10*16 + i] = 128 + 64 * $acos  (i*0.2 - 0.8);
			data[11*16 + i] = 128 + 64 * $atan  (i*0.2 - 0.8);
			data[12*16 + i] = 128 + 64 * $sinh  (i*0.2 - 0.8);
			data[13*16 + i] = 128 + 64 * $cosh  (i*0.2 - 0.8);
			data[14*16 + i] = 128 + 64 * $tanh  (i*0.2 - 0.8);
			data[15*16 + i] = 128 + 64 * $asinh (i*0.2 - 0.8);
			data[16*16 + i] = 128 + 64 * $acosh (i*0.2 - 0.8);
			data[17*16 + i] = 128 + 64 * $atanh (i*0.2 - 0.8);
		end
	end

	assign y = s < 18 ? data[s*16 + a] : 0;
endmodule

module demo_003(s, a, b, y);
	input [1:0] s;
	input [3:0] a;
	input [3:0] b;
	output [7:0] y;

	reg [7:0] data [3*16*16-1:0];
	integer i, j;

	initial begin
		for (i = 0; i < 16; i = i+1)
		for (j = 0; j < 16; j = j+1) begin
			data[0*256 + i*16 + j] = 128 + 64 * $pow   (i*0.2 - 0.8, j*0.2 - 0.8);
			data[1*256 + i*16 + j] = 128 + 64 * $atan2 (i*0.2 - 0.8, j*0.2 - 0.8);
			data[2*256 + i*16 + j] = 128 + 64 * $hypot (i*0.2 - 0.8, j*0.2 - 0.8);
		end
	end

	assign y = s < 3 ? data[s*256 + a*16 + b] : 0;
endmodule

