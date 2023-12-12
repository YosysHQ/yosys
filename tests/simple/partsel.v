module partsel_test001(input [2:0] idx, input [31:0] data, output [3:0] slice_up, slice_down);
wire [5:0] offset = idx << 2;
assign slice_up = data[offset +: 4];
assign slice_down = data[offset + 3 -: 4];
endmodule

module partsel_test002 (
	input clk, rst,
	input [7:0] a,
	input [0:7] b,
	input [1:0] s,
	output [7:0] x1, x2, x3,
	output [0:7] x4, x5, x6,
	output [7:0] y1, y2, y3,
	output [0:7] y4, y5, y6,
	output [7:0] z1, z2, z3,
	output [0:7] z4, z5, z6,
	output [7:0] w1, w2, w3,
	output [0:7] w4, w5, w6,
	output [7:0] p1, p2, p3, p4, p5, p6,
	output [0:7] q1, q2, q3, q4, q5, q6,
	output reg [7:0] r1,
	output reg [0:7] r2
);

assign x1 = a, x2 = a + b, x3 = b;
assign x4 = a, x5 = a + b, x6 = b;
assign y1 = a[4 +: 3], y2 = a[4 +: 3] + b[4 +: 3], y3 = b[4 +: 3];
assign y4 = a[4 +: 3], y5 = a[4 +: 3] + b[4 +: 3], y6 = b[4 +: 3];
assign z1 = a[4 -: 3], z2 = a[4 -: 3] + b[4 -: 3], z3 = b[4 -: 3];
assign z4 = a[4 -: 3], z5 = a[4 -: 3] + b[4 -: 3], z6 = b[4 -: 3];
assign w1 = a[6:3], w2 = a[6:3] + b[3:6], w3 = b[3:6];
assign w4 = a[6:3], w5 = a[6:3] + b[3:6], w6 = b[3:6];
assign p1 = a[s], p2 = b[s], p3 = a[s+2 +: 2], p4 = b[s+2 +: 2], p5 = a[s+2 -: 2], p6 = b[s+2 -: 2];
assign q1 = a[s], q2 = b[s], q3 = a[s+2 +: 2], q4 = b[s+2 +: 2], q5 = a[s+2 -: 2], q6 = b[s+2 -: 2];

always @(posedge clk) begin
	if (rst) begin
		{ r1, r2 } = 16'h1337 ^ {a, b};
	end else begin
		case (s)
			0: begin
				r1[3:0] <= r2[0:3] ^ x1;
				r2[4:7] <= r1[7:4] ^ x4;
			end
			1: begin
				r1[2 +: 3] <= r2[5 -: 3] + x1;
				r2[3 +: 3] <= r1[6 -: 3] + x4;
			end
			2: begin
				r1[6 -: 3] <= r2[3 +: 3] - x1;
				r2[7 -: 3] <= r1[4 +: 3] - x4;
			end
			3: begin
				r1 <= r2;
				r2 <= r1;
			end
		endcase
	end
end

endmodule

module partsel_test003(input [2:0] a, b, input [31:0] din, output [3:0] dout);
assign dout = din[a*b +: 2];
endmodule

module partsel_test004 (
	input [31:0] din,
	input signed [4:0] n,
	output reg [31:0] dout
);
	always @(*) begin
		dout = 0;
		dout[n+1 +: 2] = din[n +: 2];
	end
endmodule


module partsel_test005 (
	input [31:0] din,
	input signed [4:0] n,
	output reg [31:0] dout
);
	always @(*) begin
		dout = 0;
		dout[n+1] = din[n];
	end
endmodule

module partsel_test006 (
	input [31:-32] din,
	input signed [4:0] n,
	output reg [31:-32] dout
);
	always @(*) begin
		dout = 0;
		dout[n+1 +: 2] = din[n +: 2];
	end
endmodule


module partsel_test007 (
	input [31:-32] din,
	input signed [4:0] n,
	output reg [31:-32] dout
);
	always @(*) begin
		dout = 0;
		dout[n+1] = din[n];
	end
endmodule


module partsel_test008 (
	input [127:0] din,
	input [3:0] idx,
	input        [4:0] uoffset,
	input signed [4:0] soffset,
	output [ 7:0] dout0,
	output [ 7:0] dout1,
	output [ 7:0] dout2,
	output [ 7:0] dout3,
	output [ 3:0] dout4,
	output [ 3:0] dout5,
	output [ 3:0] dout6,
	output [ 3:0] dout7,
	output [ 3:0] dout8,
	output [11:0] dout9,
	output [11:0] dout10,
	output [11:0] dout11
);

// common: block-select with offsets
assign dout0  = din[idx*8 +uoffset +:8];
assign dout1  = din[idx*8 -uoffset +:8];
assign dout2  = din[idx*8 +soffset +:8];
assign dout3  = din[idx*8 -soffset +:8];

// only partial block used
assign dout4  = din[idx*8 +uoffset +:4];
assign dout5  = din[idx*8 -uoffset +:4];
assign dout6  = din[idx*8 +soffset +:4];
assign dout7  = din[idx*8 -soffset +:4];

// uncommon: more than one block used
assign dout8  = din[idx*8 +uoffset +:12];
assign dout9  = din[idx*8 -uoffset +:12];
assign dout10 = din[idx*8 +soffset +:12];
assign dout11 = din[idx*8 -soffset +:12];
endmodule
