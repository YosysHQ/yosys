// Test multidimensional packed arrays

typedef logic [0:3][7:0] reg2dim_t;
typedef logic  [7:0] reg8_t;
typedef reg8_t [0:3] reg2dim1_t;

module pcktest1 (
    input  logic  clk,
    input  logic [0:3][7:0] in,
    input  logic [1:0] ix,
    output reg8_t out
);
    always_ff @(posedge clk) begin
        out <= in[ix];
    end
endmodule

module pcktest2 (
    input  logic  clk,
    input  reg8_t [0:3] in,
    input  logic [1:0] ix,
    output reg8_t out
);
    always_ff @(posedge clk) begin
        out <= in[ix];
    end
endmodule

module pcktest3 (
    input  logic  clk,
    input  reg2dim_t in,
    input  logic [1:0] ix,
    output reg8_t out
);
    always_ff @(posedge clk) begin
        out <= in[ix];
    end
endmodule

module pcktest4 (
    input  logic  clk,
    input  reg2dim1_t in,
    input  logic [1:0] ix,
    output reg8_t out
);
    always_ff @(posedge clk) begin
        out <= in[ix];
    end
endmodule
