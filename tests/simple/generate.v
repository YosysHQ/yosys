
module gen_test1(clk, a, b, y);

input clk;
input [7:0] a, b;
output reg [7:0] y;

genvar i, j;
wire [15:0] tmp1;

generate

	for (i = 0; i < 8; i = i + 1) begin:gen1
		wire and_wire, or_wire;
		assign and_wire = a[i] & b[i];
		assign or_wire = a[i] | b[i];
		if (i % 2 == 0) begin:gen2true
			assign tmp1[i] = and_wire;
			assign tmp1[i+8] = or_wire;
		end else begin:gen2false
			assign tmp1[i] = or_wire;
			assign tmp1[i+8] = and_wire;
		end
	end

	for (i = 0; i < 8; i = i + 1) begin:gen3
		wire [4:0] tmp2;
		for (j = 0; j <= 4; j = j + 1) begin:gen4
			wire tmpbuf;
			assign tmpbuf = tmp1[i+2*j];
			assign tmp2[j] = tmpbuf;
		end
		always @(posedge clk)
			y[i] <= ^tmp2;
	end

endgenerate

endmodule

// ------------------------------------------

module gen_test2(clk, a, b, y);

input clk;
input [7:0] a, b;
output reg [8:0] y;

integer i;
reg [8:0] carry;

always @(posedge clk) begin
	carry[0] = 0;
	for (i = 0; i < 8; i = i + 1) begin
		casez ({a[i], b[i], carry[i]})
			3'b?11, 3'b1?1, 3'b11?:
				carry[i+1] = 1;
			default:
				carry[i+1] = 0;
		endcase
		y[i] = a[i] ^ b[i] ^ carry[i];
	end
	y[8] = carry[8];
end

endmodule

// ------------------------------------------

module gen_test3(a, b, sel, y, z);

input [3:0] a, b;
input sel;
output [3:0] y, z;

genvar i;
generate
	for (i=0; i < 2; i=i+1)
		assign y[i] = sel ? a[i] : b[i], z[i] = sel ? b[i] : a[i];
	for (i=0; i < 2; i=i+1) begin
		if (i == 0)
			assign y[2] = sel ? a[2] : b[2];
		else
			assign z[2] = sel ? a[2] : b[2];
		case (i)
		default:
			assign z[3] = sel ? a[3] : b[3];
		0:
			assign y[3] = sel ? a[3] : b[3];
		endcase
	end
endgenerate
endmodule

// ------------------------------------------

module gen_test4(a, b);

input [3:0] a;
output [3:0] b;

genvar i;
generate
	for (i=0; i < 3; i=i+1) begin : foo
		localparam PREV = i - 1;
		wire temp;
		if (i == 0)
			assign temp = a[0];
		else
			assign temp = foo[PREV].temp & a[i];
		assign b[i] = temp;
	end
endgenerate
endmodule

// ------------------------------------------

module gen_test5(input_bits, out);

parameter WIDTH = 256;
parameter CHUNK = 4;

input [WIDTH-1:0] input_bits;
output out;

genvar step, i, j;
generate
	for (step = 1; step <= WIDTH; step = step * CHUNK) begin : steps
		localparam PREV = step / CHUNK;
		localparam DIM = WIDTH / step;
		for (i = 0; i < DIM; i = i + 1) begin : outer
			localparam LAST_START = i * CHUNK;
			for (j = 0; j < CHUNK; j = j + 1) begin : inner
				wire temp;
				if (step == 1)
					assign temp = input_bits[i];
				else if (j == 0)
					assign temp = steps[PREV].outer[LAST_START].val;
				else
					assign temp
						= steps[step].outer[i].inner[j-1].temp
						& steps[PREV].outer[LAST_START + j].val;
			end
			wire val;
			assign val = steps[step].outer[i].inner[CHUNK - 1].temp;
		end
	end
endgenerate
assign out = steps[WIDTH].outer[0].val;
endmodule

// ------------------------------------------

module gen_test6(output [3:0] o);
generate
    genvar i;
    for (i = 3; i >= 0; i = i-1) begin
        assign o[i] = 1'b0;
    end
endgenerate
endmodule

// ------------------------------------------

module gen_test7;
	reg [2:0] out1;
	reg [2:0] out2;
	wire [2:0] out3;
	generate
		if (1) begin : cond
			reg [2:0] sub_out1;
			reg [2:0] sub_out2;
			wire [2:0] sub_out3;
			initial begin : init
				reg signed [31:0] x;
				x = 2 ** 2;
				out1 = x;
				sub_out1 = x;
			end
			always @* begin : proc
				reg signed [31:0] x;
				x = 2 ** 1;
				out2 = x;
				sub_out2 = x;
			end
			genvar x;
			for (x = 0; x < 3; x = x + 1) begin
				assign out3[x] = 1;
				assign sub_out3[x] = 1;
			end
		end
	endgenerate

// `define VERIFY
`ifdef VERIFY
	assert property (out1 == 4);
	assert property (out2 == 2);
	assert property (out3 == 7);
	assert property (cond.sub_out1 == 4);
	assert property (cond.sub_out2 == 2);
	assert property (cond.sub_out3 == 7);
`endif
endmodule

// ------------------------------------------

module gen_test8;

// `define VERIFY
`ifdef VERIFY
	`define ASSERT(expr) assert property (expr);
`else
	`define ASSERT(expr)
`endif

	wire [1:0] x = 2'b11;
	generate
		if (1) begin : A
			wire [1:0] x;
			if (1) begin : B
				wire [1:0] x = 2'b00;
				`ASSERT(x == 0)
				`ASSERT(A.x == 2)
				`ASSERT(A.C.x == 1)
				`ASSERT(A.B.x == 0)
				`ASSERT(gen_test8.x == 3)
				`ASSERT(gen_test8.A.x == 2)
				`ASSERT(gen_test8.A.C.x == 1)
				`ASSERT(gen_test8.A.B.x == 0)
			end
			if (1) begin : C
				wire [1:0] x = 2'b01;
				`ASSERT(x == 1)
				`ASSERT(A.x == 2)
				`ASSERT(A.C.x == 1)
				`ASSERT(A.B.x == 0)
				`ASSERT(gen_test8.x == 3)
				`ASSERT(gen_test8.A.x == 2)
				`ASSERT(gen_test8.A.C.x == 1)
				`ASSERT(gen_test8.A.B.x == 0)
			end
			assign x = B.x ^ 2'b11 ^ C.x;
			`ASSERT(x == 2)
			`ASSERT(A.x == 2)
			`ASSERT(A.C.x == 1)
			`ASSERT(A.B.x == 0)
			`ASSERT(gen_test8.x == 3)
			`ASSERT(gen_test8.A.x == 2)
			`ASSERT(gen_test8.A.C.x == 1)
			`ASSERT(gen_test8.A.B.x == 0)
		end
	endgenerate

	`ASSERT(x == 3)
	`ASSERT(A.x == 2)
	`ASSERT(A.C.x == 1)
	`ASSERT(A.B.x == 0)
	`ASSERT(gen_test8.x == 3)
	`ASSERT(gen_test8.A.x == 2)
	`ASSERT(gen_test8.A.C.x == 1)
	`ASSERT(gen_test8.A.B.x == 0)
endmodule

// ------------------------------------------

module gen_test9;

// `define VERIFY
`ifdef VERIFY
	`define ASSERT(expr) assert property (expr);
`else
	`define ASSERT(expr)
`endif

	wire [1:0] w = 2'b11;
	generate
		begin : A
			wire [1:0] x;
			begin : B
				wire [1:0] y = 2'b00;
				`ASSERT(w == 3)
				`ASSERT(x == 2)
				`ASSERT(y == 0)
				`ASSERT(A.x == 2)
				`ASSERT(A.C.z == 1)
				`ASSERT(A.B.y == 0)
				`ASSERT(gen_test9.w == 3)
				`ASSERT(gen_test9.A.x == 2)
				`ASSERT(gen_test9.A.C.z == 1)
				`ASSERT(gen_test9.A.B.y == 0)
			end
			begin : C
				wire [1:0] z = 2'b01;
				`ASSERT(w == 3)
				`ASSERT(x == 2)
				`ASSERT(z == 1)
				`ASSERT(A.x == 2)
				`ASSERT(A.C.z == 1)
				`ASSERT(A.B.y == 0)
				`ASSERT(gen_test9.w == 3)
				`ASSERT(gen_test9.A.x == 2)
				`ASSERT(gen_test9.A.C.z == 1)
				`ASSERT(gen_test9.A.B.y == 0)
			end
			assign x = B.y ^ 2'b11 ^ C.z;
			`ASSERT(x == 2)
			`ASSERT(A.x == 2)
			`ASSERT(A.C.z == 1)
			`ASSERT(A.B.y == 0)
			`ASSERT(gen_test9.w == 3)
			`ASSERT(gen_test9.A.x == 2)
			`ASSERT(gen_test9.A.C.z == 1)
			`ASSERT(gen_test9.A.B.y == 0)
		end
	endgenerate

	`ASSERT(w == 3)
	`ASSERT(A.x == 2)
	`ASSERT(A.C.z == 1)
	`ASSERT(A.B.y == 0)
	`ASSERT(gen_test9.w == 3)
	`ASSERT(gen_test9.A.x == 2)
	`ASSERT(gen_test9.A.C.z == 1)
	`ASSERT(gen_test9.A.B.y == 0)
endmodule
