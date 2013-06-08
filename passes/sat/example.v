
module example001(a, y);

input [15:0] a;
output y;

wire gt = a > 12345;
wire lt = a < 12345;
assign y = !gt && !lt;

endmodule

// ------------------------------------

module example002(a, y);

input [3:0] a;
output y;
reg [1:0] t1, t2;

always @* begin
	casex (a)
		16'b1xxx:
			t1 <= 1;
		16'bx1xx:
			t1 <= 2;
		16'bxx1x:
			t1 <= 3;
		16'bxxx1:
			t1 <= 4;
		default:
			t1 <= 0;
	endcase
	casex (a)
		16'b1xxx:
			t2 <= 1;
		16'b01xx:
			t2 <= 2;
		16'b001x:
			t2 <= 3;
		16'b0001:
			t2 <= 4;
		default:
			t2 <= 0;
	endcase
end

assign y = t1 != t2;

endmodule

// ------------------------------------

module example003(a_shl, a_shr, a_sshl, a_sshr, sh, y_shl, y_shr, y_sshl, y_sshr);

input [7:0] a_shl, a_shr;
input signed [7:0] a_sshl, a_sshr;
input [3:0] sh;

output [7:0] y_shl = a_shl << sh, y_shr = a_shr >> sh;
output signed [7:0] y_sshl = a_sshl <<< sh, y_sshr = a_sshr >>> sh;

endmodule

// ------------------------------------

module example004(clk, rst, y);

input clk, rst;
output y;

reg [3:0] counter;

always @(posedge clk)
	case (1'b1)
		rst, counter == 9:
			counter <= 0;
		default:
			counter <= counter+1;
	endcase

assign y = counter == 12;

endmodule

