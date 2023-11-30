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

module BRAM_TDP #(parameter AWIDTH = 10,
parameter DWIDTH = 36)(
	clk_a,
	rce_a,
	ra_a,
	rq_a,
	wce_a,
	wa_a,
	wd_a,

	clk_b,
	rce_b,
	ra_b,
	rq_b,
	wce_b,
	wa_b,
	wd_b
);

	input                   clk_a;
	input                   rce_a;
	input      [AWIDTH-1:0] ra_a;
	output reg [DWIDTH-1:0] rq_a;
	input                   wce_a;
	input      [AWIDTH-1:0] wa_a;
	input      [DWIDTH-1:0] wd_a;

	input                   clk_b;
	input                   rce_b;
	input      [AWIDTH-1:0] ra_b;
	output reg [DWIDTH-1:0] rq_b;
	input                   wce_b;
	input      [AWIDTH-1:0] wa_b;
	input      [DWIDTH-1:0] wd_b;

	(* no_rw_check = 1 *)
	reg [DWIDTH-1:0] memory[0:(1<<AWIDTH)-1];

	wire [AWIDTH-1:0] a_a = rce_a ? ra_a : wa_a;
	wire [AWIDTH-1:0] a_b = rce_b ? ra_b : wa_b;

	wire ce_a = rce_a || wce_a;
	wire ce_b = rce_b || wce_b;

	always @(posedge clk_a) begin
		if (ce_a) begin
			if (wce_a)
				memory[a_a] <= wd_a;
			rq_a <= memory[a_a];
		end
	end

	always @(posedge clk_b) begin
		if (ce_b) begin
			if (wce_b)
				memory[a_b] <= wd_b;
			rq_b <= memory[a_b];
		end
	end

endmodule