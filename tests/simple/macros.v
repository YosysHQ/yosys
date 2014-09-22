
module test_def(a, y);

`define MSB_LSB_SEP :
`define get_msb(off, len) ((off)+(len)-1)
`define get_lsb(off, len) (off)
`define sel_bits(offset, len) `get_msb(offset, len) `MSB_LSB_SEP `get_lsb(offset, len)

input [31:0] a;
output [7:0] y;

assign y = a[`sel_bits(16, 8)];

endmodule

// ---------------------------------------------------

module test_ifdef(a, y);

input [2:0] a;
output reg [31:0] y;

always @* begin
	y = 0;

	`undef X
	`ifdef X
		y = y + 42;
	`else
		`undef  A
		`undef  B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`undef  A
		`define B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`undef  B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`define B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef  A
		`undef  B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`undef  A
		`define B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`undef  B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`define B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef A
		`ifdef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`ifdef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef A
		`ifndef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`ifndef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
	`endif

	`define X
	`ifdef X
		`undef  A
		`undef  B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`undef  A
		`define B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`undef  B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`define B
		`ifdef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef  A
		`undef  B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`undef  A
		`define B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`undef  B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`define B
		`ifndef A
			y = (y << 1) | a[0];
		`elsif B
			y = (y << 1) | a[1];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef A
		`ifdef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`ifdef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		// ------------------------------------
		`undef A
		`ifndef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
		`define A
		`ifndef A
			y = (y << 1) | a[0];
		`else
			y = (y << 1) | a[2];
		`endif
	`else
		y = y + 42;
	`endif
end

endmodule

`define SIZE 4 // comment supported in this part
module test_comment_in_macro ( din_a, dout_a );
input [`SIZE-1:0] din_a;
output [`SIZE-1:0] dout_a;
assign dout_a = din_a | `SIZE'ha;
endmodule
