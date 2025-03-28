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

module \$__QL_MUL20X18 (input [19:0] A, input [17:0] B, output [37:0] Y);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH = 0;
    parameter B_WIDTH = 0;
    parameter Y_WIDTH = 0;

    wire [19:0] a;
    wire [17:0] b;
    wire [37:0] z;

    assign a = (A_WIDTH == 20) ? A :
               (A_SIGNED) ? {{(20 - A_WIDTH){A[A_WIDTH-1]}}, A} :
                            {{(20 - A_WIDTH){1'b0}},         A};

    assign b = (B_WIDTH == 18) ? B :
               (B_SIGNED) ? {{(18 - B_WIDTH){B[B_WIDTH-1]}}, B} :
                            {{(18 - B_WIDTH){1'b0}},         B};

    (* is_inferred=1 *)
    dsp_t1_20x18x64_cfg_ports _TECHMAP_REPLACE_ (
        .a_i                (a),
        .b_i                (b),
        .acc_fir_i          (6'd0),
        .z_o                (z),

        .feedback_i         (3'd0),
        .load_acc_i         (1'b0),
        .unsigned_a_i       (!A_SIGNED),
        .unsigned_b_i       (!B_SIGNED),

        .output_select_i    (3'd0),
        .saturate_enable_i  (1'b0),
        .shift_right_i      (6'd0),
        .round_i            (1'b0),
        .subtract_i         (1'b0),
        .register_inputs_i  (1'b0)
    );

    assign Y = z;

endmodule

module \$__QL_MUL10X9 (input [9:0] A, input [8:0] B, output [18:0] Y);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH = 0;
    parameter B_WIDTH = 0;
    parameter Y_WIDTH = 0;

    wire [ 9:0] a;
    wire [ 8:0] b;
    wire [18:0] z;

    assign a = (A_WIDTH == 10) ? A :
               (A_SIGNED) ? {{(10 - A_WIDTH){A[A_WIDTH-1]}}, A} :
                            {{(10 - A_WIDTH){1'b0}},         A};

    assign b = (B_WIDTH ==  9) ? B :
               (B_SIGNED) ? {{( 9 - B_WIDTH){B[B_WIDTH-1]}}, B} :
                            {{( 9 - B_WIDTH){1'b0}},         B};

    (* is_inferred=1 *)
    dsp_t1_10x9x32_cfg_ports _TECHMAP_REPLACE_ (
        .a_i                (a),
        .b_i                (b),
        .acc_fir_i          (6'd0),
        .z_o                (z),

        .feedback_i         (3'd0),
        .load_acc_i         (1'b0),
        .unsigned_a_i       (!A_SIGNED),
        .unsigned_b_i       (!B_SIGNED),

        .output_select_i    (3'd0),
        .saturate_enable_i  (1'b0),
        .shift_right_i      (6'd0),
        .round_i            (1'b0),
        .subtract_i         (1'b0),
        .register_inputs_i  (1'b0)
    );


    assign Y = z;

endmodule
