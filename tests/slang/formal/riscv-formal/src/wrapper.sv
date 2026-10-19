/*
 *  NERV -- Naive Educational RISC-V Processor
 *
 *  Copyright (C) 2020  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

module rvfi_wrapper (
	input         clock,
	input         reset,
	`RVFI_OUTPUTS
	`RVFI_BUS_OUTPUTS
);
	(* keep *) `rvformal_rand_reg stall;
	(* keep *) `rvformal_rand_reg [31:0] imem_data;
	(* keep *) `rvformal_rand_reg [31:0] dmem_rdata;
	(* keep *) `rvformal_rand_reg [31:0] irq;

`ifdef NERV_FAULT
	(* keep *) `rvformal_rand_reg imem_fault;
	(* keep *) `rvformal_rand_reg dmem_fault;
`else
	wire imem_fault = 0;
	wire dmem_fault = 0;
`endif

	(* keep *) wire trap;

	(* keep *) wire [31:0] imem_addr;

	(* keep *) wire        dmem_valid;
	(* keep *) wire [31:0] dmem_addr;
	(* keep *) wire [ 3:0] dmem_wstrb;
	(* keep *) wire [31:0] dmem_wdata;

	nerv uut (
		.clock      (clock    ),
		.reset      (reset    ),
		.stall      (stall    ),
		.trap       (trap     ),

		.imem_addr  (imem_addr ),
		.imem_data  (imem_data ),

		.dmem_valid (dmem_valid),
		.dmem_addr  (dmem_addr ),
		.dmem_wstrb (dmem_wstrb),
		.dmem_wdata (dmem_wdata),
		.dmem_rdata (dmem_rdata),

`ifdef NERV_FAULT
		.imem_fault (imem_fault),
		.dmem_fault (dmem_fault),
`endif

		.irq (irq),

		`RVFI_CONN32
	);

`ifdef RISCV_FORMAL_BUS

`define RISCV_FORMAL_CHANNEL_SIGNAL(channels, width, name) \
	(* keep *) reg [(width) - 1:0] imem_``name; assign rvfi_``name[0 * (width) +: (width)] = imem_``name;
`RVFI_BUS_SIGNALS
`undef RISCV_FORMAL_CHANNEL_SIGNAL

`define RISCV_FORMAL_CHANNEL_SIGNAL(channels, width, name) \
	(* keep *) reg [(width) - 1:0] dmem_``name; assign rvfi_``name[1 * (width) +: (width)] = dmem_``name;
`RVFI_BUS_SIGNALS
`undef RISCV_FORMAL_CHANNEL_SIGNAL


	reg [31:0] imem_addr_q;

	always @(posedge clock) begin
		if (!stall)
			imem_addr_q <= imem_addr;
	end

	always @* begin
		imem_bus_addr  = imem_addr_q;
		imem_bus_insn  = 1;
		imem_bus_data  = 0;
		imem_bus_rmask = 4'b1111;
		imem_bus_wmask = 4'b0000;
		imem_bus_rdata = imem_data;
		imem_bus_wdata = 0;
		imem_bus_fault = imem_fault;
		imem_bus_valid = !stall;
	end;

	reg        dmem_valid_q;
	reg [31:0] dmem_addr_q;
	reg [ 3:0] dmem_wstrb_q;
	reg [31:0] dmem_wdata_q;


	(* keep *) `rvformal_rand_reg [31:0] next_dmem_rdata;
	reg [31:0] next_dmem_rdata_q;

`ifdef NERV_FAULT
	(* keep *) `rvformal_rand_reg [31:0] next_dmem_fault;
	reg [31:0] next_dmem_fault_q;
`endif

	always @(posedge clock) begin
		if (!stall) begin
			next_dmem_rdata_q <= next_dmem_rdata;
`ifdef NERV_FAULT
			next_dmem_fault_q <= next_dmem_fault;
`endif
		end
	end

	always @* begin
		if (!stall) begin
			assume (dmem_rdata == next_dmem_rdata_q);
`ifdef NERV_FAULT
			assume (dmem_fault == next_dmem_fault_q);
`endif
		end
		dmem_bus_addr  = dmem_addr;
		dmem_bus_insn  = 0;
		dmem_bus_data  = 1;
		dmem_bus_rmask = dmem_wstrb ? 4'b0000 : 4'b1111;
		dmem_bus_wmask = dmem_wstrb;
		dmem_bus_rdata = next_dmem_rdata;
		dmem_bus_wdata = dmem_wdata;
		dmem_bus_fault = next_dmem_fault;
		dmem_bus_valid = !stall && dmem_valid;
	end;

`endif

`ifdef NERV_FAIRNESS
	reg [2:0] stalled = 0;
	always @(posedge clock) begin
		stalled <= {stalled, stall};
		assume (~stalled);
	end
`endif
endmodule
