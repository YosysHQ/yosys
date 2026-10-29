// Copyright (C) 2017  Claire Xenia Wolf <claire@yosyshq.com>
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
// ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
// ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
// OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

module rvfi_testbench (
	`ifdef RISCV_FORMAL_UNBOUNDED
	`ifdef RISCV_FORMAL_TRIG_CYCLE
		input trig,
	`endif
	`ifdef RISCV_FORMAL_CHECK_CYCLE
		input check,
	`endif
	`endif
	input clock, reset
);
	`RVFI_WIRES
	`RVFI_BUS_WIRES

// Unsure if this is the right abstraction
// might be better to get $initstate working with read_slang
`ifdef READ_SLANG
    reg initial_state = 1'b1;

    always @(posedge clock)
        initial_state <= 1'b0;

    always @*
        assume (reset == initial_state);
`elsif YOSYS
    always @*
        assume (reset == $initstate);
`endif

	reg [7:0] cycle_reg = 0;
	wire [7:0] cycle = reset ? 8'd 0 : cycle_reg;

	always @(posedge clock) begin
		cycle_reg <= reset ? 8'd 1 : cycle_reg + (cycle_reg != 8'h ff);
	end

	`RISCV_FORMAL_CHECKER checker_inst (
		.clock  (clock),
		.reset  (cycle < `RISCV_FORMAL_RESET_CYCLES),
`ifdef RISCV_FORMAL_TRIG_CYCLE
`ifdef RISCV_FORMAL_UNBOUNDED
		.trig   (trig),
`else
		.trig   (cycle == `RISCV_FORMAL_TRIG_CYCLE),
`endif
`endif
`ifdef RISCV_FORMAL_CHECK_CYCLE
`ifdef RISCV_FORMAL_UNBOUNDED
		.check   (check),
`else
		.check  (cycle == `RISCV_FORMAL_CHECK_CYCLE),
`endif
`endif
		`RVFI_CONN
		`RVFI_BUS_CONN
	);

	rvfi_wrapper wrapper (
		.clock (clock),
		.reset (reset),
		`RVFI_CONN
		`RVFI_BUS_CONN
	);

`ifdef RISCV_FORMAL_ASSUME
`include "assume_stmts.vh"
`endif
endmodule

module rvfi_seq #(
	parameter [1023:0] seq = "",
	parameter integer N = 1
) (
	input clock,
	output reg [N-1:0] dout,
	output reg en
);
	localparam seqlen = $clog2(seq) / 8;

	integer cycle = 0;
	wire [31:0] position = seqlen - cycle;
	wire [7:0] ch = seq >> (8*position);

	always @(posedge clock) begin
	cycle <= cycle + 1;
	end

	always @* begin
		en = |ch;
		dout = 4'b xxxx;
		case (ch)
			"0", "_": dout = 0;
			"1": dout = 1;
			"2": dout = 2;
			"3": dout = 3;
			"4": dout = 4;
			"5": dout = 5;
			"6": dout = 6;
			"7": dout = 7;
			"8": dout = 8;
			"9": dout = 9;
			"A", "a": dout = 10;
			"B", "b": dout = 11;
			"C", "c": dout = 12;
			"D", "d": dout = 13;
			"E", "e": dout = 14;
			"F", "f", "-": dout = 15;
			"X", "x", " ": begin
				dout = 4'b xxxx;
				en = 0;
			end
		endcase
	end
endmodule

module rvfi_assume_seq #(
	parameter [1023:0] seq = "",
	parameter integer N = 1
) (
	input clock,
	input [N-1:0] din
);
	wire en;
	wire [N-1:0] dout;
	rvfi_seq #(seq, N) seq_inst (clock, dout, en);
	always @* if (en) assume (din == dout);
endmodule
