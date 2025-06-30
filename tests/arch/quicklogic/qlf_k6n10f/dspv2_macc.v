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

module macc_simple (
    input  wire       clk,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [8:0] Z
);

    always @(posedge clk)
        Z <= Z + (A * B);

endmodule

module macc_simple_clr (
    input  wire       clk,
    input  wire       clr,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [6:0] Z
);

    always @(posedge clk)
        if (clr) Z <=     (A * B);
        else     Z <= Z + (A * B);

endmodule

module macc_simple_arst (
    input  wire       clk,
    input  wire       rst,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [8:0] Z
);

    always @(posedge clk or posedge rst)
        if (rst) Z <= 0;
        else     Z <= Z + (A * B);

endmodule

module macc_simple_ena (
    input  wire       clk,
    input  wire       ena,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [8:0] Z
);

    always @(posedge clk)
        if (ena) Z <= Z + (A * B);

endmodule

module macc_simple_arst_clr_ena (
    input  wire       clk,
    input  wire       rst,
    input  wire       clr,
    input  wire       ena,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [7:0] Z
);

    always @(posedge clk or posedge rst)
        if (rst)     Z <= 0;
        else if (ena) begin
            if (clr) Z <=     (A * B);
            else     Z <= Z + (A * B);
        end

endmodule

module macc_simple_preacc (
    input  wire       clk,
    input  wire [4:0] A,
    input  wire [4:0] B,
    output wire [7:0] Z
);

    reg [7:0] acc;

    assign Z = acc + (A * B);

    always @(posedge clk)
        acc <= Z;

endmodule

module macc_simple_preacc_clr (
    input  wire       clk,
    input  wire       clr,
    input  wire [5:0] A,
    input  wire [5:0] B,
    output reg  [7:0] Z
);

    reg [7:0] acc;

    assign Z = (clr) ? (A * B) : (acc + (A * B));

    always @(posedge clk)
        acc <= Z;

endmodule

module macc_simple_signed (
    input  wire        clk,
    input  wire signed [4:0] A,
    input  wire signed [4:0] B,
    output reg  signed [7:0] Z
);

    always @(posedge clk)
        Z <= Z + (A * B);

endmodule

module macc_simple_signed_subtract (
    input  wire        clk,
    input  wire signed [4:0] A,
    input  wire signed [4:0] B,
    output reg  signed [7:0] Z
);

    always @(posedge clk)
        Z <= Z - (A * B);

endmodule

