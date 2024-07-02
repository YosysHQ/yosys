/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

module reg_c(
    input clk,

    // active high
    input en_A,
    input en_B,
    input en_D,
    input en_P,

    // active low
    input srst_A,
    input srst_B,
    input srst_D,
    input srst_P,

    // active low
    input arst_D,

    input srst_C,
    input arst_C,


    input signed [5:0] in_A,
    input signed [4:0] in_B,
    input signed [4:0] in_C,
    input signed [4:0] in_D,
    
    
    output reg [11:0] out_P

);


// MACC_PA takes active low resets
wire srst_A_N;
wire srst_B_N;
wire srst_C_N;
wire srst_D_N;
wire srst_P_N;
assign srst_A_N = ~srst_A;
assign srst_B_N = ~srst_B;
assign srst_C_N = ~srst_C;
assign srst_D_N = ~srst_D;
assign srst_P_N = ~srst_P;

// input reg
reg signed [5:0] reg_A;
reg signed [4:0] reg_B;
reg signed [4:0] reg_C;
reg signed [4:0] reg_D;

// sync reset A
always@(posedge clk) begin
    // if (~srst_A_N) begin
    if (srst_A_N) begin
        reg_A = 6'b000000;
    end else begin
        reg_A = in_A;
    end
end



// sync reset B
always@(posedge clk) begin
    if (srst_B_N) begin
        reg_B = 5'b00000;
    end else begin
        reg_B = in_B;
    end
end



// async reset D
always@(posedge clk, negedge arst_D) begin
    if (~arst_D) begin
        reg_D = 5'b00000;
    end else begin
        reg_D = in_D;
    end
end

// sync reset C
always@(posedge clk) begin
    if (srst_C_N) begin
        reg_C = 5'b00000;
    end else begin
        reg_C = in_C;
    end
end



// sync reset P
always@(posedge clk) begin
    if (srst_P_N) begin
        out_P = 12'h000;
    end else begin
        out_P = reg_A * (reg_B + reg_D) + reg_C;
    end
end

endmodule