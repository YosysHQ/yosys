module \$__MUL32X18 (input [31:0] A, input [17:0] B, output [49:0] Y);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH = 32;
    parameter B_WIDTH = 18;
    parameter Y_WIDTH = 50;

    dspv2_32x18x64_cfg_ports _TECHMAP_REPLACE_ (
        .a_i(A),
        .b_i(B),
        .c_i(18'd0),
        .z_o(Y),

        .clock_i(1'bx),
        .reset_i(1'bx),
        .acc_reset_i(1'b0),
        .feedback_i(3'd0),
        .load_acc_i(1'b0),
        .output_select_i(3'd0),
        .a_cin_i(32'dx),
        .b_cin_i(18'dx),
        .z_cin_i(50'dx),
/* TODO: connect to dummy wires?
        .a_cout_o(),
        .b_cout_o(),
        .z_cout_o(),
*/
    );
endmodule

module \$__MUL16X9 (input [15:0] A, input [8:0] B, output [24:0] Y);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH = 16;
    parameter B_WIDTH = 9;
    parameter Y_WIDTH = 25;

    dspv2_16x9x32_cfg_ports _TECHMAP_REPLACE_ (
        .a_i(A),
        .b_i(B),
        .c_i(9'd0),
        .z_o(Y),

        .clock_i(1'bx),
        .reset_i(1'bx),
        .acc_reset_i(1'b0),
        .feedback_i(3'd0),
        .load_acc_i(1'b0),
        .output_select_i(3'd0),
        .a_cin_i(32'dx),
        .b_cin_i(18'dx),
        .z_cin_i(50'dx),
/* TODO: connect to dummy wires?
        .a_cout_o(),
        .b_cout_o(),
        .z_cout_o(),
*/
    );
endmodule
