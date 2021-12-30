module top (
    input signed [1:0] a,
    input signed [2:0] b,
    output signed [4:0] c
);
    assign c = 2'(a) * b;
endmodule
