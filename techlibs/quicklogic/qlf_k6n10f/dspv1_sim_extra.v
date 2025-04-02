// Copyright 2020-2022 F4PGA Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

`timescale 1ps/1ps

`default_nettype none

// dsp_t1_20x18x64_cfg_ports but with input wire f_mode_i
// This is a yosys-specific extension beyond the vendor-provided model
module dsp_t1_20x18x64_cfg_ports_fracturable (
	input  wire [19:0] a_i,
	input  wire [17:0] b_i,
	input  wire [ 5:0] acc_fir_i,
	output wire [37:0] z_o,
	output wire [17:0] dly_b_o,

	(* clkbuf_sink *)
	input  wire        clock_i,
	input  wire        reset_i,

	input  wire [ 2:0] feedback_i,
	input  wire        load_acc_i,
	input  wire        unsigned_a_i,
	input  wire        unsigned_b_i,

	input  wire [ 2:0] output_select_i,
	input  wire        saturate_enable_i,
	input  wire [ 5:0] shift_right_i,
	input  wire        round_i,
	input  wire        subtract_i,
	input  wire        register_inputs_i,
	input  wire        f_mode_i
);

	parameter [19:0] COEFF_0 = 20'd0;
	parameter [19:0] COEFF_1 = 20'd0;
	parameter [19:0] COEFF_2 = 20'd0;
	parameter [19:0] COEFF_3 = 20'd0;

	QL_DSP2 #(
		.MODE_BITS({COEFF_3, COEFF_2, COEFF_1, COEFF_0})
	) dsp (
		.a(a_i),
		.b(b_i),
		.z(z_o),
		.dly_b(dly_b_o),

		.f_mode(f_mode_i),  // 20x18x64 DSP

		.acc_fir(acc_fir_i),
		.feedback(feedback_i),
		.load_acc(load_acc_i),

		.unsigned_a(unsigned_a_i),
		.unsigned_b(unsigned_b_i),

		.clk(clock_i),
		.reset(reset_i),

		.saturate_enable(saturate_enable_i),
		.output_select(output_select_i),
		.round(round_i),
		.shift_right(shift_right_i),
		.subtract(subtract_i),
		.register_inputs(register_inputs_i)
	);
endmodule
