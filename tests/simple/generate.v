
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
