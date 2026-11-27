module top
#(parameter X_WIDTH=8, Y_WIDTH=8, C_WIDTH=16, A_WIDTH=16)
(
    input signed [X_WIDTH-1:0] x,
    input signed [Y_WIDTH-1:0] y,
    input signed [C_WIDTH-1:0] c,
    output signed [A_WIDTH-1:0] A
);
    assign A = x * y + c;
endmodule

module sub_top
#(parameter X_WIDTH=8, Y_WIDTH=8, C_WIDTH=16, A_WIDTH=16)
(
    input signed [X_WIDTH-1:0] x,
    input signed [Y_WIDTH-1:0] y,
    input signed [C_WIDTH-1:0] c,
    output signed [A_WIDTH-1:0] A
);
    assign A = x * y - c;
endmodule

module twoproduct_top
#(parameter X_WIDTH=8, Y_WIDTH=8, C_WIDTH=16, A_WIDTH=16)
(
    input signed [X_WIDTH-1:0] x,
    input signed [Y_WIDTH-1:0] y,
    input signed [C_WIDTH-1:0] c,
    output signed [A_WIDTH-1:0] A
);
    wire signed [X_WIDTH+Y_WIDTH-1:0] p = x * y;
    assign A = p + p;
endmodule

module unsigned_top
#(parameter X_WIDTH=8, Y_WIDTH=8, C_WIDTH=16, A_WIDTH=16)
(
    input [X_WIDTH-1:0] x,
    input [Y_WIDTH-1:0] y,
    input [C_WIDTH-1:0] c,
    output [A_WIDTH-1:0] A
);
    assign A = x * y + c;
endmodule
