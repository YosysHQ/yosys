
module test1(clk, a, b, y);

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

module test2(clk, a, b, y);

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

