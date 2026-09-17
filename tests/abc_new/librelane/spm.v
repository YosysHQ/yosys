// https://github.com/librelane/librelane/blob/f24e0ea5db2260719e9a0c7d51d07db74a87fa23/librelane/examples/spm/src/spm.v

// Copyright 2023 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// (Parameterized) Unsigned Serial/Parallel Multiplier:
// - Multiplicand x (Input bit-serially)
// - Multiplier a (All bits at the same time/Parallel)
// - Product y (Output bit-serial)
module spm #(parameter bits=32) (
    input clk,
    input rst,
    input x,
    input[bits-1: 0] a,
    output y
);
    wire[bits: 0] y_chain;
    assign y_chain[0] = 0;
    assign y = y_chain[bits];

    wire[bits-1:0] a_flip;
    genvar i;
    generate 
        for (i = 0; i < bits; i = i + 1) begin : flip_block
            assign a_flip[i] = a[bits - i - 1];
        end 
    endgenerate

    delayed_serial_adder dsa[bits-1:0](
        .clk(clk),
        .rst(rst),
        .x(x),
        .a(a_flip),
        .y_in(y_chain[bits-1:0]),
        .y_out(y_chain[bits:1])
    );

endmodule

module delayed_serial_adder(
    input clk,
    input rst,
    input x,
    input a,
    input y_in,
    output reg y_out
);
    reg last_carry;
    wire last_carry_next;
    wire y_out_next;

    wire g = x & a;
    assign {last_carry_next, y_out_next} = g + y_in + last_carry;

    always @ (posedge clk or negedge rst) begin
        if (!rst) begin
            last_carry <= 1'b0;
            y_out <= 1'b0;
        end else begin
            last_carry <= last_carry_next;
            y_out <= y_out_next;
        end
    end
endmodule
