module pass_through_a(
    input wire [31:0] inp,
    output wire [31:0] out
);
    assign out[31:0] = inp[31:0];
endmodule

module top_a(
    input wire signed [31:0] inp,
    output wire signed [31:0] out
);
    pass_through_a pt(inp[31:0], out[31:0]);
endmodule

// tests both module declaration orderings

module top_b(
    input wire signed [31:0] inp,
    output wire signed [31:0] out
);
    pass_through_b pt(inp[31:0], out[31:0]);
endmodule

module pass_through_b(
    input wire [31:0] inp,
    output wire [31:0] out
);
    assign out[31:0] = inp[31:0];
endmodule
