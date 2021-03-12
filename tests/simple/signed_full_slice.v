module pass_through(
    input wire [31:0] inp,
    output wire [31:0] out
);
    assign out = inp;
endmodule

module top(
    input wire signed [31:0] inp,
    output wire [31:0] out
);
    pass_through pt(inp[31:0], out[31:0]);
endmodule
