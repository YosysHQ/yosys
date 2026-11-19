// Signed multiply for GW5A DSP boundary tests (the GW5A multipliers are
// signed-only, so signed operands exercise the routing boundaries cleanly).
module top
#(parameter X_WIDTH=8, Y_WIDTH=8, A_WIDTH=16)
(
    input signed [X_WIDTH-1:0] x,
    input signed [Y_WIDTH-1:0] y,
    output signed [A_WIDTH-1:0] A
);
    assign A = x * y;
endmodule
